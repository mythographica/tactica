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
const graph_1 = require("./graph");
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
 * Run type generation. Returns 0 on success; 1 when the graph identity law
 * aborted the run (failures printed, no .tactica output written).
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
    // Path-aware graph reference resolution (identity law): the generator
    // resolves names through the same relative-first/root/unique tiers the
    // analyzer uses; the analyzer's own value/import tiers already vetted the
    // type strings during extraction
    const referenceResolver = (simpleName, anchor) => {
        const refResult = (0, graph_1.resolveGraphTypeReference)(graph, simpleName, anchor);
        if (refResult.status === 'unique') {
            return refResult.node;
        }
        if (refResult.status === 'ambiguous') {
            return 'ambiguous';
        }
        return undefined;
    };
    const generator = new generator_1.TypesGenerator(graph, options.esm, options.outputDir, referenceResolver);
    // Check if module augmentation mode is requested (legacy)
    const useModuleAugmentation = options.globalAugmentation === false;
    // Generate everything into memory FIRST — the hard-fail law below may
    // abort the run, and no .tactica output at all may be written then
    let generatedTypes;
    let registryTypes;
    let outputPath;
    if (useModuleAugmentation) {
        // Legacy mode: generate global augmentation file (index.d.ts)
        generatedTypes = generator.generateGlobalAugmentation();
    }
    else {
        // Default mode: generate types.ts for manual imports
        generatedTypes = generator.generateTypesFile();
        // Generate registry.ts for type-safe lookup() function
        registryTypes = generator.generateTypeRegistry();
    }
    // HARD FAIL (graph identity law): same-namespace duplicate mnemonica
    // definitions, plus graph references that stay ambiguous after
    // path-aware resolution or resolve to nothing. Print every failure with
    // all its locations and write NO .tactica output at all.
    const fatalErrors = [...analyzer.getResolutionErrors(), ...generator.getResolutionErrors()];
    if (fatalErrors.length > 0) {
        const seen = new Set();
        let printed = 0;
        for (const error of fatalErrors) {
            const key = `${error.message}|${error.locations.join('|')}`;
            if (seen.has(key)) {
                continue;
            }
            seen.add(key);
            printed++;
            console.error(`tactica: ${error.message}`);
            for (const location of error.locations) {
                console.error(`  at ${location}`);
            }
        }
        console.error(`tactica: aborting — ${printed} resolution failure(s); no .tactica output written`);
        return 1;
    }
    const writer = new writer_1.TypesWriter(options.outputDir);
    if (useModuleAugmentation) {
        // Legacy mode: write global augmentation file (index.d.ts)
        outputPath = writer.writeGlobalAugmentation(generatedTypes);
    }
    else {
        // Default mode: write types.ts for manual imports
        outputPath = writer.writeTypesFile(generatedTypes);
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
        // The analyzer's own lookup law, against the same complete graph the
        // usages pass resolved with — a lookup() initializer the analyzer
        // accepted (e.g. an imported Holder.lookup('Token')) lands the same
        // fullPath in scopes.json instead of starving the creation-graph
        // anchors. Rejected lookups stay typePath-less here; the analyzer
        // already hard-failed the run above.
        resolveLookup: (call) => {
            const resolved = analyzer.resolveLookupCallPath(call);
            return resolved;
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
    return 0;
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
            const code = run(options);
            if (code) {
                process.exit(code);
            }
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQWc2Qlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUE5NUI1Qix1Q0FBeUI7QUFDekIsMkNBQTZCO0FBQzdCLG1DQUF1QztBQUN2QywrQ0FBaUM7QUFDakMseUNBQStDO0FBQy9DLCtEQUEyRDtBQUMzRCwyQ0FFcUI7QUFDckIscUNBQXVDO0FBQ3ZDLGlEQUFvRDtBQUNwRCxxREFBd0Q7QUFDeEQscUNBRWtCO0FBQ2xCLG1DQUVpQjtBQTBCakI7O0dBRUc7QUFDSCxTQUFTLFNBQVMsQ0FBRSxJQUFjO0lBQ2pDLE1BQU0sT0FBTyxHQUFlLEVBQUUsQ0FBQztJQUUvQixLQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRSxDQUFDO1FBQ3RDLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBRSxDQUFDLENBQUUsQ0FBQztRQUV0QixRQUFRLEdBQUcsRUFBRSxDQUFDO1lBQ2QsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFNBQVM7Z0JBQ2IsT0FBTyxDQUFDLEtBQUssR0FBRyxJQUFJLENBQUM7Z0JBQ3JCLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssV0FBVztnQkFDZixPQUFPLENBQUMsT0FBTyxHQUFHLElBQUksQ0FBRSxFQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUM5QixNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFVBQVU7Z0JBQ2QsT0FBTyxDQUFDLFNBQVMsR0FBRyxJQUFJLENBQUUsRUFBRSxDQUFDLENBQUUsQ0FBQztnQkFDaEMsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxXQUFX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ZXNDb250ZW50IjpbIiMhL3Vzci9iaW4vZW52IG5vZGVcbid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgZnMgZnJvbSAnZnMnO1xuaW1wb3J0ICogYXMgcGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCB7IGNyZWF0ZVJlcXVpcmUgfSBmcm9tICdtb2R1bGUnO1xuaW1wb3J0ICogYXMgdHMgZnJvbSAndHlwZXNjcmlwdCc7XG5pbXBvcnQgeyBNbmVtb25pY2FBbmFseXplciB9IGZyb20gJy4vYW5hbHl6ZXInO1xuaW1wb3J0IHsgVG9wb2xvZ2ljYUFuYWx5emVyIH0gZnJvbSAnLi90b3BvbG9naWNhLWFuYWx5emVyJztcbmltcG9ydCB7XG5cdFR5cGVzR2VuZXJhdG9yLCBHcmFwaFJlZmVyZW5jZVJlc29sdmVyIFxufSBmcm9tICcuL2dlbmVyYXRvcic7XG5pbXBvcnQgeyBUeXBlc1dyaXRlciB9IGZyb20gJy4vd3JpdGVyJztcbmltcG9ydCB7IE1vZHVsZUdyYXBoQnVpbGRlciB9IGZyb20gJy4vbW9kdWxlLWdyYXBoJztcbmltcG9ydCB7IENyZWF0aW9uR3JhcGhCdWlsZGVyIH0gZnJvbSAnLi9jcmVhdGlvbi1ncmFwaCc7XG5pbXBvcnQge1xuXHRMb2NhbFNjb3BlV2Fsa2VyLCBTY29wZVR5cGVSZXNvbHZlclxufSBmcm9tICcuL3Njb3Blcyc7XG5pbXBvcnQge1xuXHRyZXNvbHZlR3JhcGhUeXBlUmVmZXJlbmNlLCBUeXBlR3JhcGhJbXBsIFxufSBmcm9tICcuL2dyYXBoJztcbmltcG9ydCB7XG5cdFRhY3RpY2FDb25maWcsIFR5cGVOb2RlLCBFRFNJbmZvLCBTY29wZUFuYWx5c2lzXG59IGZyb20gJy4vdHlwZXMnO1xuaW1wb3J0IHsgVGFjdGljYVBsdWdpbiB9IGZyb20gJy4vcGx1Z2lucyc7XG5cbi8qKlxuICogQ0xJIGVudHJ5IHBvaW50IGZvciBUYWN0aWNhXG4gKlxuICogUnVucyB0aGUgYW5hbHl6ZXIgb3ZlciBhIHRzY29uZmlnIHByb2plY3QgYW5kIHdyaXRlcyAudGFjdGljYS8gb3V0cHV0XG4gKi9cblxuaW50ZXJmYWNlIENMSU9wdGlvbnMgZXh0ZW5kcyBUYWN0aWNhQ29uZmlnIHtcblx0d2F0Y2g/OiBib29sZWFuO1xuXHRwcm9qZWN0Pzogc3RyaW5nO1xuXHRoZWxwPzogYm9vbGVhbjtcblx0LyoqIEN1c3RvbSB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIHRvIHNjYW4gKi9cblx0dG9wb2xvZ2ljYURpcnM/OiBzdHJpbmdbXTtcblx0LyoqIEFkZCAuanMgZXh0ZW5zaW9ucyB0byByZWxhdGl2ZSBpbXBvcnRzIGZvciBFU00gTm9kZU5leHQgcmVzb2x1dGlvbiAqL1xuXHRlc20/OiBib29sZWFuO1xuXHQvKiogRW5hYmxlIEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdHJhY2tpbmcgKi9cblx0ZWRzPzogYm9vbGVhbjtcblx0LyoqIFByb2dyYW1tYXRpYyBwbHVnaW5zOyBjb25maWctZmlsZSBwbHVnaW5zIGFyZSBhcHBlbmRlZCBhZnRlciB0aGVzZSAqL1xuXHRwbHVnaW5zPzogVGFjdGljYVBsdWdpbltdO1xufVxuXG4vKipcbiAqIFBhcnNlIGNvbW1hbmQgbGluZSBhcmd1bWVudHNcbiAqL1xuZnVuY3Rpb24gcGFyc2VBcmdzIChhcmdzOiBzdHJpbmdbXSk6IENMSU9wdGlvbnMge1xuXHRjb25zdCBvcHRpb25zOiBDTElPcHRpb25zID0ge307XG5cblx0Zm9yIChsZXQgaSA9IDA7IGkgPCBhcmdzLmxlbmd0aDsgaSsrKSB7XG5cdFx0Y29uc3QgYXJnID0gYXJnc1sgaSBdO1xuXG5cdFx0c3dpdGNoIChhcmcpIHtcblx0XHRjYXNlICctdyc6XG5cdFx0Y2FzZSAnLS13YXRjaCc6XG5cdFx0XHRvcHRpb25zLndhdGNoID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1wJzpcblx0XHRjYXNlICctLXByb2plY3QnOlxuXHRcdFx0b3B0aW9ucy5wcm9qZWN0ID0gYXJnc1sgKytpIF07XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctbyc6XG5cdFx0Y2FzZSAnLS1vdXRwdXQnOlxuXHRcdFx0b3B0aW9ucy5vdXRwdXREaXIgPSBhcmdzWyArK2kgXTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1pJzpcblx0XHRjYXNlICctLWluY2x1ZGUnOlxuXHRcdFx0b3B0aW9ucy5pbmNsdWRlID0gKG9wdGlvbnMuaW5jbHVkZSB8fCBbXSkuY29uY2F0KGFyZ3NbICsraSBdLnNwbGl0KCcsJykpO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLWUnOlxuXHRcdGNhc2UgJy0tZXhjbHVkZSc6XG5cdFx0XHRvcHRpb25zLmV4Y2x1ZGUgPSAob3B0aW9ucy5leGNsdWRlIHx8IFtdKS5jb25jYXQoYXJnc1sgKytpIF0uc3BsaXQoJywnKSk7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctbSc6XG5cdFx0Y2FzZSAnLS1tb2R1bGUtYXVnbWVudGF0aW9uJzpcblx0XHRcdG9wdGlvbnMuZ2xvYmFsQXVnbWVudGF0aW9uID0gZmFsc2U7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctdic6XG5cdFx0Y2FzZSAnLS12ZXJib3NlJzpcblx0XHRcdG9wdGlvbnMudmVyYm9zZSA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctdCc6XG5cdFx0Y2FzZSAnLS10b3BvbG9naWNhJzpcblx0XHRcdG9wdGlvbnMudG9wb2xvZ2ljYURpcnMgPSAob3B0aW9ucy50b3BvbG9naWNhRGlycyB8fCBbXSkuY29uY2F0KGFyZ3NbICsraSBdLnNwbGl0KCcsJykpO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLS1lc20nOlxuXHRcdFx0b3B0aW9ucy5lc20gPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLS1lZHMnOlxuXHRcdFx0b3B0aW9ucy5lZHMgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLS1uby1lZHMnOlxuXHRcdFx0b3B0aW9ucy5lZHMgPSBmYWxzZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1oJzpcblx0XHRjYXNlICctLWhlbHAnOlxuXHRcdFx0b3B0aW9ucy5oZWxwID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdH1cblx0fVxuXG5cdHJldHVybiBvcHRpb25zO1xufVxuXG4vKipcbiAqIFByaW50IGhlbHAgbWVzc2FnZVxuICovXG5mdW5jdGlvbiBwcmludEhlbHAgKCk6IHZvaWQge1xuXHRjb25zb2xlLmxvZyhgXG5UYWN0aWNhIC0gVHlwZSBkZWZpbml0aW9uIGdlbmVyYXRvciBmb3IgTW5lbW9uaWNhXG5cblVzYWdlOiB0YWN0aWNhIFtvcHRpb25zXVxuXG5PcHRpb25zOlxuICAtdywgLS13YXRjaCAgICAgICAgICAgICAgIFdhdGNoIGZvciBmaWxlIGNoYW5nZXMgYW5kIHJlZ2VuZXJhdGUgdHlwZXNcbiAgLXAsIC0tcHJvamVjdCAgICAgICAgICAgICBQYXRoIHRvIHRzY29uZmlnLmpzb24gKGRlZmF1bHQ6IC4vdHNjb25maWcuanNvbilcbiAgLW8sIC0tb3V0cHV0ICAgICAgICAgICAgICBPdXRwdXQgZGlyZWN0b3J5IGZvciBnZW5lcmF0ZWQgdHlwZXMgKGRlZmF1bHQ6IC50YWN0aWNhKVxuICAtaSwgLS1pbmNsdWRlICAgICAgICAgICAgIENvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIGZpbGUgcGF0dGVybnMgdG8gaW5jbHVkZVxuICAtZSwgLS1leGNsdWRlICAgICAgICAgICAgIENvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIGZpbGUgcGF0dGVybnMgdG8gZXhjbHVkZVxuICAtdCwgLS10b3BvbG9naWNhICAgICAgICAgIENvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXMgdG8gc2NhblxuICAtbSwgLS1tb2R1bGUtYXVnbWVudGF0aW9uIFVzZSBtb2R1bGUgYXVnbWVudGF0aW9uIGluc3RlYWQgb2YgZ2xvYmFsIChsZWdhY3kgbW9kZSlcbiAgLS1lc20gICAgICAgICAgICAgICAgICAgICBBZGQgLmpzIGV4dGVuc2lvbnMgdG8gcmVsYXRpdmUgaW1wb3J0cyAoTm9kZU5leHQgRVNNKVxuICAtLWVkcyAgICAgICAgICAgICAgICAgICAgIEVuYWJsZSBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHRyYWNraW5nXG4gIC0tbm8tZWRzICAgICAgICAgICAgICAgICAgRGlzYWJsZSBFRFMgdHJhY2tpbmdcbiAgLXYsIC0tdmVyYm9zZSAgICAgICAgICAgICBFbmFibGUgdmVyYm9zZSBsb2dnaW5nXG4gIC1oLCAtLWhlbHAgICAgICAgICAgICAgICAgU2hvdyB0aGlzIGhlbHAgbWVzc2FnZVxuXG5Db25maWd1cmF0aW9uOlxuICBGcmFtZXdvcmsgaW5zdHJ1bWVudGF0aW9uIHZvY2FidWxhcnkgaXMgc3VwcGxpZWQgYnkgcGx1Z2lucy4gUGxhY2UgYVxuICAudGFjdGljYS5qcyAob3IgdGFjdGljYS5jb25maWcuanMpIG5leHQgdG8geW91ciB0c2NvbmZpZy5qc29uOlxuXG4gICAgICBtb2R1bGUuZXhwb3J0cyA9IHsgcGx1Z2luczogWyAneW91ci1mcmFtZXdvcmstYWRhcHRlci90YWN0aWNhJyBdIH07XG5cbiAgRW50cmllcyBhcmUgbW9kdWxlIHNwZWNpZmllcnMgKHJlcXVpcmVkIHJlbGF0aXZlIHRvIHRoZSBjb25maWcgZmlsZSkgb3JcbiAgaW5saW5lIHBsdWdpbiBvYmplY3RzLiBXaXRob3V0IHBsdWdpbnMsIGluc3RydW1lbnRhdGlvbi5qc29uIHBvaW50cyA9IFtdLlxuXG5FeGFtcGxlczpcbiAgdGFjdGljYSAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICMgR2VuZXJhdGUgdHlwZXMgd2l0aCBnbG9iYWwgYXVnbWVudGF0aW9uIChkZWZhdWx0KVxuICB0YWN0aWNhIC0td2F0Y2ggICAgICAgICAgICAgICAgICAgICAgIyBXYXRjaCBtb2RlXG4gIHRhY3RpY2EgLS1tb2R1bGUtYXVnbWVudGF0aW9uICAgICAgICAjIFVzZSBsZWdhY3kgbW9kdWxlIGF1Z21lbnRhdGlvbiBtb2RlXG4gIHRhY3RpY2EgLS1wcm9qZWN0IC4vc3JjL3RzY29uZmlnLmpzb24gIyBDdXN0b20gdHNjb25maWcgcGF0aFxuICB0YWN0aWNhIC0tb3V0cHV0IC4vdHlwZXMvbW5lbW9uaWNhICAgIyBDdXN0b20gb3V0cHV0IGRpcmVjdG9yeVxuICB0YWN0aWNhIC0tdG9wb2xvZ2ljYSAuL3NyYy9haS10eXBlcyAgIyBTY2FuIHNwZWNpZmljIHRvcG9sb2dpY2EgZGlyZWN0b3J5XG5gKTtcbn1cblxuLyoqXG4gKiBGaW5kIHRzY29uZmlnLmpzb25cbiAqL1xuZnVuY3Rpb24gZmluZFRzQ29uZmlnIChwcm9qZWN0UGF0aD86IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdGlmIChwcm9qZWN0UGF0aCkge1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKHByb2plY3RQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHByb2plY3RQYXRoO1xuXHRcdH1cblx0XHR0aHJvdyBuZXcgRXJyb3IoYFByb2plY3QgZmlsZSBub3QgZm91bmQ6ICR7cHJvamVjdFBhdGh9YCk7XG5cdH1cblxuXHQvLyBMb29rIGZvciB0c2NvbmZpZy5qc29uIGluIGN1cnJlbnQgZGlyZWN0b3J5IGFuZCBwYXJlbnQgZGlyZWN0b3JpZXNcblx0bGV0IGN1cnJlbnREaXIgPSBwcm9jZXNzLmN3ZCgpO1xuXHR3aGlsZSAoY3VycmVudERpciAhPT0gcGF0aC5kaXJuYW1lKGN1cnJlbnREaXIpKSB7XG5cdFx0Y29uc3QgdHNjb25maWdQYXRoID0gcGF0aC5qb2luKGN1cnJlbnREaXIsICd0c2NvbmZpZy5qc29uJyk7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmModHNjb25maWdQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHRzY29uZmlnUGF0aDtcblx0XHR9XG5cdFx0Y3VycmVudERpciA9IHBhdGguZGlybmFtZShjdXJyZW50RGlyKTtcblx0fVxuXG5cdHJldHVybiB1bmRlZmluZWQ7XG59XG5cbi8qKlxuICogTG9hZCBUeXBlU2NyaXB0IHByb2dyYW0gZnJvbSB0c2NvbmZpZ1xuICovXG5mdW5jdGlvbiBsb2FkUHJvZ3JhbSAodHNjb25maWdQYXRoOiBzdHJpbmcpOiB0cy5Qcm9ncmFtIHtcblx0Y29uc3QgY29uZmlnRmlsZSA9IHRzLnJlYWRDb25maWdGaWxlKHRzY29uZmlnUGF0aCwgdHMuc3lzLnJlYWRGaWxlKTtcblxuXHRpZiAoY29uZmlnRmlsZS5lcnJvcikge1xuXHRcdGNvbnN0IGVycm9yVGV4dCA9IHRzLmZsYXR0ZW5EaWFnbm9zdGljTWVzc2FnZVRleHQoXG5cdFx0XHRjb25maWdGaWxlLmVycm9yLm1lc3NhZ2VUZXh0LFxuXHRcdFx0J1xcbidcblx0XHQpO1xuXHRcdHRocm93IG5ldyBFcnJvcihgRXJyb3IgcmVhZGluZyB0c2NvbmZpZzogJHtlcnJvclRleHR9YCk7XG5cdH1cblxuXHRjb25zdCBwYXJzZWRDb25maWcgPSB0cy5wYXJzZUpzb25Db25maWdGaWxlQ29udGVudChcblx0XHRjb25maWdGaWxlLmNvbmZpZyxcblx0XHR0cy5zeXMsXG5cdFx0cGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aClcblx0KTtcblxuXHRpZiAocGFyc2VkQ29uZmlnLmVycm9ycy5sZW5ndGggPiAwKSB7XG5cdFx0Y29uc3QgZXJyb3JNZXNzYWdlcyA9IHBhcnNlZENvbmZpZy5lcnJvcnMubWFwKGUgPT5cblx0XHRcdHRzLmZsYXR0ZW5EaWFnbm9zdGljTWVzc2FnZVRleHQoZS5tZXNzYWdlVGV4dCwgJ1xcbicpKTtcblx0XHR0aHJvdyBuZXcgRXJyb3IoYEVycm9yIHBhcnNpbmcgdHNjb25maWc6ICR7ZXJyb3JNZXNzYWdlcy5qb2luKCdcXG4nKX1gKTtcblx0fVxuXG5cdGNvbnN0IHByb2dyYW0gPSB0cy5jcmVhdGVQcm9ncmFtKHtcblx0XHRyb290TmFtZXMgOiBwYXJzZWRDb25maWcuZmlsZU5hbWVzLFxuXHRcdG9wdGlvbnMgICA6IHBhcnNlZENvbmZpZy5vcHRpb25zLFxuXHR9KTtcblxuXHRyZXR1cm4gcHJvZ3JhbTtcbn1cblxuLyoqXG4gKiBMb29rIHVwIGEgdmFyaWFibGUgYnkgbmFtZSBzdGFydGluZyBmcm9tIGEgc2NvcGUsIHdhbGtpbmcgb3V0d2FyZCB0aHJvdWdoXG4gKiBwYXJlbnRTY29wZUlkLiBUaGUgaW5uZXJtb3N0IGJpbmRpbmcgd2lucyBldmVuIHdoZW4gaXQgY2FycmllcyBubyB0eXBlUGF0aFxuICogKHNoYWRvd2luZyBob25lc3R5IOKAlCBhbiB1bnR5cGVkIGxvY2FsIHNoYWRvd3MgYSB0eXBlZCBvdXRlciBvbmUpLlxuICovXG5mdW5jdGlvbiByZXNvbHZlU2NvcGVkVmFyaWFibGVUeXBlUGF0aCAoXG5cdG5hbWU6IHN0cmluZyxcblx0c2NvcGVJZDogc3RyaW5nLFxuXHRzY29wZUFuYWx5c2lzOiBTY29wZUFuYWx5c2lzXG4pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRsZXQgY3VycmVudDogc3RyaW5nIHwgdW5kZWZpbmVkID0gc2NvcGVJZDtcblx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRjb25zdCB2YXJpYWJsZSA9IHNjb3BlQW5hbHlzaXMudmFyaWFibGVzLmdldChgJHtjdXJyZW50fSMke25hbWV9YCk7XG5cdFx0aWYgKHZhcmlhYmxlKSB7XG5cdFx0XHRjb25zdCB7IHR5cGVQYXRoIH0gPSB2YXJpYWJsZTtcblx0XHRcdHJldHVybiB0eXBlUGF0aDtcblx0XHR9XG5cdFx0Y3VycmVudCA9IHNjb3BlQW5hbHlzaXMuc2NvcGVzLmdldChjdXJyZW50KT8ucGFyZW50U2NvcGVJZDtcblx0fVxuXHRyZXR1cm4gdW5kZWZpbmVkO1xufVxuXG4vKipcbiAqIEpvaW4gZGF0YSBmb3IgbW5lbW9ncmFwaGljYSdzIHdyYXBwZXJzIGxheWVyOiBwaW4gZWFjaCB3cmFwIGVudHJ5IHRvIHRoZVxuICogc2NvcGUgaG9sZGluZyBpdHMgY2FsbCBzaXRlLCBhbmQgcmVzb2x2ZSB0aGUgd3JhcHBlZCBpbnN0YW5jZSBhcmd1bWVudCdzXG4gKiBtbmVtb25pY2EgdHlwZSB0aHJvdWdoIHRoZSBzY29wZS12YXJpYWJsZSBjaGFpbi5cbiAqL1xuZnVuY3Rpb24gYXR0YWNoV3JhcEpvaW5EYXRhIChcblx0ZWRzOiBNYXA8c3RyaW5nLCBFRFNJbmZvW10+LFxuXHRzY29wZVdhbGtlcjogTG9jYWxTY29wZVdhbGtlcixcblx0c2NvcGVBbmFseXNpczogU2NvcGVBbmFseXNpc1xuKTogdm9pZCB7XG5cdGZvciAoY29uc3QgZW50cmllcyBvZiBlZHMudmFsdWVzKCkpIHtcblx0XHRmb3IgKGNvbnN0IGVudHJ5IG9mIGVudHJpZXMpIHtcblx0XHRcdGlmIChlbnRyeS5raW5kICE9PSAnd3JhcCcpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBob2xkZXJTY29wZUlkID0gc2NvcGVXYWxrZXIuZmluZEhvbGRlclNjb3BlSWQoZW50cnkubG9jYXRpb24pO1xuXHRcdFx0aWYgKCFob2xkZXJTY29wZUlkKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0ZW50cnkuc2NvcGVJZCA9IGhvbGRlclNjb3BlSWQ7XG5cdFx0XHRpZiAoIWVudHJ5Lmluc3RhbmNlQXJnKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgd3JhcHNUeXBlUGF0aCA9IHJlc29sdmVTY29wZWRWYXJpYWJsZVR5cGVQYXRoKFxuXHRcdFx0XHRlbnRyeS5pbnN0YW5jZUFyZyxcblx0XHRcdFx0aG9sZGVyU2NvcGVJZCxcblx0XHRcdFx0c2NvcGVBbmFseXNpc1xuXHRcdFx0KTtcblx0XHRcdGlmICh3cmFwc1R5cGVQYXRoKSB7XG5cdFx0XHRcdGVudHJ5LndyYXBzVHlwZVBhdGggPSB3cmFwc1R5cGVQYXRoO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxufVxuXG4vKipcbiAqIFJlbmRlciB0eXBlIGhpZXJhcmNoeSBhcyBhbiBBU0NJSSB0cmVlIHN0cmluZy5cbiAqL1xuZnVuY3Rpb24gcmVuZGVyVHlwZUhpZXJhcmNoeSAoZ3JhcGg6IFR5cGVHcmFwaEltcGwpOiBzdHJpbmcge1xuXHRjb25zdCBsaW5lczogc3RyaW5nW10gPSBbICdUeXBlIEhpZXJhcmNoeSAoVHJpZSk6JyBdO1xuXG5cdGZ1bmN0aW9uIHJlbmRlck5vZGUgKG5vZGU6IFR5cGVOb2RlLCBwcmVmaXggPSAnJywgaXNMYXN0ID0gdHJ1ZSk6IHZvaWQge1xuXHRcdGNvbnN0IGNvbm5lY3RvciA9IGlzTGFzdCA/ICfilJTilIDilIAgJyA6ICfilJzilIDilIAgJztcblx0XHQvLyBVc2Ugbm9kZS5mdWxsUGF0aCBkaXJlY3RseSBhbmQgY29udmVydCBkb3RzIHRvIHVuZGVyc2NvcmVzXG5cdFx0Y29uc3QgaW5zdGFuY2VOYW1lID0gbm9kZS5mdWxsUGF0aC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRsaW5lcy5wdXNoKGAke3ByZWZpeH0ke2Nvbm5lY3Rvcn0ke2luc3RhbmNlTmFtZX1gKTtcblxuXHRcdGNvbnN0IGNoaWxkcmVuID0gQXJyYXkuZnJvbShub2RlLmNoaWxkcmVuLnZhbHVlcygpKTtcblx0XHRjb25zdCBuZXdQcmVmaXggPSBwcmVmaXggKyAoaXNMYXN0ID8gJyAgICAnIDogJ+KUgiAgICcpO1xuXG5cdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBjaGlsZHJlbi5sZW5ndGg7IGkrKykge1xuXHRcdFx0cmVuZGVyTm9kZShjaGlsZHJlblsgaSBdLCBuZXdQcmVmaXgsIGkgPT09IGNoaWxkcmVuLmxlbmd0aCAtIDEpO1xuXHRcdH1cblx0fVxuXG5cdGNvbnN0IHJvb3RzID0gQXJyYXkuZnJvbShncmFwaC5yb290cy52YWx1ZXMoKSk7XG5cdGZvciAobGV0IGkgPSAwOyBpIDwgcm9vdHMubGVuZ3RoOyBpKyspIHtcblx0XHRyZW5kZXJOb2RlKHJvb3RzWyBpIF0sICcnLCBpID09PSByb290cy5sZW5ndGggLSAxKTtcblx0fVxuXHQvLyBFbXB0eSBsaW5lIGF0IGVuZFxuXHRsaW5lcy5wdXNoKCcnKTtcblxuXHRjb25zdCByZXN1bHQgPSBsaW5lcy5qb2luKCdcXG4nKTtcblx0cmV0dXJuIHJlc3VsdDtcbn1cblxuLyoqXG4gKiBQcmludCB0eXBlIGhpZXJhcmNoeSB0byB0aGUgY29uc29sZS5cbiAqL1xuZnVuY3Rpb24gcHJpbnRUeXBlSGllcmFyY2h5IChncmFwaDogVHlwZUdyYXBoSW1wbCk6IHZvaWQge1xuXHRjb25zdCBvdXRwdXQgPSByZW5kZXJUeXBlSGllcmFyY2h5KGdyYXBoKTtcblx0Y29uc29sZS5sb2cob3V0cHV0KTtcbn1cblxuLyoqXG4gKiBDaGVjayBpZiBAbW5lbW9uaWNhL2RpdmUgaXMgcHJlc2VudCBpbiBwYWNrYWdlLmpzb24gZGVwZW5kZW5jaWVzXG4gKi9cbmZ1bmN0aW9uIGhhc0RpdmVEZXBlbmRlbmN5IChwcm9qZWN0RGlyOiBzdHJpbmcpOiBib29sZWFuIHtcblx0Y29uc3QgcGFja2FnZUpzb25QYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsICdwYWNrYWdlLmpzb24nKTtcblx0aWYgKCFmcy5leGlzdHNTeW5jKHBhY2thZ2VKc29uUGF0aCkpIHtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblx0dHJ5IHtcblx0XHRjb25zdCBjb250ZW50ID0gZnMucmVhZEZpbGVTeW5jKHBhY2thZ2VKc29uUGF0aCwgJ3V0Zi04Jyk7XG5cdFx0Y29uc3QgcGtnID0gSlNPTi5wYXJzZShjb250ZW50KTtcblx0XHRjb25zdCBkZXBzID0gcGtnLmRlcGVuZGVuY2llcyB8fCB7fTtcblx0XHRjb25zdCBkZXZEZXBzID0gcGtnLmRldkRlcGVuZGVuY2llcyB8fCB7fTtcblx0XHRjb25zdCBwZWVyRGVwcyA9IHBrZy5wZWVyRGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdHJldHVybiAnQG1uZW1vbmljYS9kaXZlJyBpbiBkZXBzIHx8ICdAbW5lbW9uaWNhL2RpdmUnIGluIGRldkRlcHMgfHwgJ0BtbmVtb25pY2EvZGl2ZScgaW4gcGVlckRlcHM7XG5cdH0gY2F0Y2gge1xuXHRcdHJldHVybiBmYWxzZTtcblx0fVxufVxuXG4vKipcbiAqIFNjYW4gZm9yIHRvcG9sb2dpY2EgZGlyZWN0b3J5IHN0cnVjdHVyZXNcbiAqL1xuZnVuY3Rpb24gc2NhblRvcG9sb2dpY2FEaXJlY3RvcmllcyAocHJvamVjdERpcjogc3RyaW5nLCBjdXN0b21EaXJzPzogc3RyaW5nW10pOiBzdHJpbmdbXSB7XG5cdGNvbnN0IGRpcnM6IHN0cmluZ1tdID0gW107XG5cblx0Ly8gRmlyc3QsIGFkZCBjdXN0b20gZGlyZWN0b3JpZXMgaWYgc3BlY2lmaWVkXG5cdGlmIChjdXN0b21EaXJzKSB7XG5cdFx0Zm9yIChjb25zdCBkaXIgb2YgY3VzdG9tRGlycykge1xuXHRcdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguaXNBYnNvbHV0ZShkaXIpID8gZGlyIDogcGF0aC5qb2luKHByb2plY3REaXIsIGRpcik7XG5cdFx0XHRpZiAoZnMuZXhpc3RzU3luYyhkaXJQYXRoKSAmJiBmcy5zdGF0U3luYyhkaXJQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHRcdGRpcnMucHVzaChkaXJQYXRoKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnNvbGUud2FybihgV2FybmluZzogVG9wb2xvZ2ljYSBkaXJlY3Rvcnkgbm90IGZvdW5kOiAke2RpclBhdGh9YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0Ly8gVGhlbiBhdXRvLWRpc2NvdmVyIHN0YW5kYXJkIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXNcblx0Y29uc3QgcG9zc2libGVEaXJzID0gWyAnYWktdHlwZXMnLCAndHlwZXMnLCAndG9wb2xvZ2ljYS10eXBlcycgXTtcblxuXHRmb3IgKGNvbnN0IGRpck5hbWUgb2YgcG9zc2libGVEaXJzKSB7XG5cdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguam9pbihwcm9qZWN0RGlyLCBkaXJOYW1lKTtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyhkaXJQYXRoKSAmJiBmcy5zdGF0U3luYyhkaXJQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHQvLyBBdm9pZCBkdXBsaWNhdGVzXG5cdFx0XHRpZiAoIWRpcnMuaW5jbHVkZXMoZGlyUGF0aCkpIHtcblx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8vIEFsc28gc2NhbiBzcmMvIHN1YmRpcmVjdG9yeVxuXHRjb25zdCBzcmNQYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsICdzcmMnKTtcblx0aWYgKGZzLmV4aXN0c1N5bmMoc3JjUGF0aCkgJiYgZnMuc3RhdFN5bmMoc3JjUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdGZvciAoY29uc3QgZGlyTmFtZSBvZiBwb3NzaWJsZURpcnMpIHtcblx0XHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmpvaW4oc3JjUGF0aCwgZGlyTmFtZSk7XG5cdFx0XHRpZiAoZnMuZXhpc3RzU3luYyhkaXJQYXRoKSAmJiBmcy5zdGF0U3luYyhkaXJQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHRcdC8vIEF2b2lkIGR1cGxpY2F0ZXNcblx0XHRcdFx0aWYgKCFkaXJzLmluY2x1ZGVzKGRpclBhdGgpKSB7XG5cdFx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIGRpcnM7XG59XG5cbi8qKlxuICogQ29uZmlnIGZpbGUgY2FuZGlkYXRlcyAoZXNsaW50LXN0eWxlIHByb2plY3QgY29uZmlnKSwgc2VhcmNoZWQgbmV4dCB0b1xuICogdGhlIHJlc29sdmVkIHRzY29uZmlnIGZpcnN0LCB0aGVuIGluIHRoZSBjdXJyZW50IHdvcmtpbmcgZGlyZWN0b3J5LlxuICovXG5jb25zdCBDT05GSUdfRklMRV9OQU1FUyA9IFsgJy50YWN0aWNhLmpzJywgJ3RhY3RpY2EuY29uZmlnLmpzJyBdO1xuXG5pbnRlcmZhY2UgVGFjdGljYUNvbmZpZ0ZpbGUge1xuXHRwbHVnaW5zPzogQXJyYXk8VGFjdGljYVBsdWdpbiB8IHN0cmluZz47XG59XG5cbi8qKlxuICogTG9hZCBmcmFtZXdvcmstdm9jYWJ1bGFyeSBwbHVnaW5zOiBwcm9ncmFtbWF0aWMgb3B0aW9ucyBmaXJzdCwgdGhlbiB0aGVcbiAqIHByb2plY3QgY29uZmlnIGZpbGUuIFN0cmluZyBlbnRyaWVzIGFyZSBtb2R1bGUgc3BlY2lmaWVycyByZXF1aXJlZFxuICogcmVsYXRpdmUgdG8gdGhlIGNvbmZpZyBmaWxlIChlLmcuIGFuIGFkYXB0ZXIgcGFja2FnZSdzIHBsdWdpbiBzdWJwYXRoKS5cbiAqIFdpdGhvdXQgYSBjb25maWcgZmlsZSBhbmQgd2l0aG91dCBwcm9ncmFtbWF0aWMgcGx1Z2lucyB0aGUgYW5hbHl6ZXJcbiAqIHN0YXlzIGZyYW1ld29yay1ibGluZCBhbmQgaW5zdHJ1bWVudGF0aW9uLmpzb24gY2FycmllcyBlbXB0eSBwb2ludHMuXG4gKi9cbmZ1bmN0aW9uIGxvYWRUYWN0aWNhUGx1Z2lucyAocHJvamVjdERpcjogc3RyaW5nLCBvcHRpb25zOiBDTElPcHRpb25zKTogVGFjdGljYVBsdWdpbltdIHtcblx0Y29uc3QgcGx1Z2luczogVGFjdGljYVBsdWdpbltdID0gWyAuLi4ob3B0aW9ucy5wbHVnaW5zIHx8IFtdKSBdO1xuXG5cdGNvbnN0IHNlYXJjaERpcnMgPSBbIHByb2plY3REaXIgXTtcblx0Y29uc3QgY3dkID0gcHJvY2Vzcy5jd2QoKTtcblx0aWYgKGN3ZCAhPT0gcHJvamVjdERpcikge1xuXHRcdHNlYXJjaERpcnMucHVzaChjd2QpO1xuXHR9XG5cblx0bGV0IGNvbmZpZ1BhdGg6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0Zm9yIChjb25zdCBkaXIgb2Ygc2VhcmNoRGlycykge1xuXHRcdGZvciAoY29uc3QgbmFtZSBvZiBDT05GSUdfRklMRV9OQU1FUykge1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlID0gcGF0aC5qb2luKGRpciwgbmFtZSk7XG5cdFx0XHRpZiAoZnMuZXhpc3RzU3luYyhjYW5kaWRhdGUpKSB7XG5cdFx0XHRcdGNvbmZpZ1BhdGggPSBjYW5kaWRhdGU7XG5cdFx0XHRcdGJyZWFrO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoY29uZmlnUGF0aCkge1xuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXHR9XG5cblx0aWYgKCFjb25maWdQYXRoKSB7XG5cdFx0cmV0dXJuIHBsdWdpbnM7XG5cdH1cblxuXHQvLyBjcmVhdGVSZXF1aXJlIGFuY2hvcmVkIGF0IHRoZSBjb25maWcgZmlsZTogdGhlIGNvbmZpZydzIG93biBpbXBvcnRzXG5cdC8vIGFuZCBzdHJpbmcgcGx1Z2luIHNwZWNpZmllcnMgcmVzb2x2ZSBhZ2FpbnN0IHRoZSBwcm9qZWN0J3MgbW9kdWxlc1xuXHRjb25zdCBjb25maWdSZXF1aXJlID0gY3JlYXRlUmVxdWlyZShjb25maWdQYXRoKTtcblx0Y29uc3QgbG9hZGVkID0gY29uZmlnUmVxdWlyZShjb25maWdQYXRoKTtcblx0Y29uc3QgY29uZmlnOiBUYWN0aWNhQ29uZmlnRmlsZSA9IGxvYWRlZCAmJiB0eXBlb2YgbG9hZGVkID09PSAnb2JqZWN0JyAmJiAnZGVmYXVsdCcgaW4gbG9hZGVkXG5cdFx0PyBsb2FkZWQuZGVmYXVsdFxuXHRcdDogbG9hZGVkO1xuXHRjb25zdCBlbnRyaWVzID0gY29uZmlnICYmIEFycmF5LmlzQXJyYXkoY29uZmlnLnBsdWdpbnMpID8gY29uZmlnLnBsdWdpbnMgOiBbXTtcblxuXHRmb3IgKGNvbnN0IGVudHJ5IG9mIGVudHJpZXMpIHtcblx0XHRpZiAodHlwZW9mIGVudHJ5ICE9PSAnc3RyaW5nJykge1xuXHRcdFx0cGx1Z2lucy5wdXNoKGVudHJ5KTtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblx0XHRjb25zdCBtb2QgPSBjb25maWdSZXF1aXJlKGVudHJ5KTtcblx0XHRjb25zdCBwbHVnaW46IFRhY3RpY2FQbHVnaW4gPSBtb2QgJiYgdHlwZW9mIG1vZCA9PT0gJ29iamVjdCcgJiYgJ2RlZmF1bHQnIGluIG1vZFxuXHRcdFx0PyBtb2QuZGVmYXVsdFxuXHRcdFx0OiBtb2Q7XG5cdFx0cGx1Z2lucy5wdXNoKHBsdWdpbik7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3QgbmFtZXMgPSBwbHVnaW5zLm1hcChwbHVnaW4gPT4gcGx1Z2luLm5hbWUgfHwgJyh1bm5hbWVkKScpLmpvaW4oJywgJyk7XG5cdFx0Y29uc29sZS5sb2coYExvYWRlZCB0YWN0aWNhIGNvbmZpZzogJHtjb25maWdQYXRofSAocGx1Z2luczogJHtuYW1lcyB8fCAnbm9uZSd9KWApO1xuXHR9XG5cblx0cmV0dXJuIHBsdWdpbnM7XG59XG5cbi8qKlxuICogUnVuIHR5cGUgZ2VuZXJhdGlvbi4gUmV0dXJucyAwIG9uIHN1Y2Nlc3M7IDEgd2hlbiB0aGUgZ3JhcGggaWRlbnRpdHkgbGF3XG4gKiBhYm9ydGVkIHRoZSBydW4gKGZhaWx1cmVzIHByaW50ZWQsIG5vIC50YWN0aWNhIG91dHB1dCB3cml0dGVuKS5cbiAqL1xuZnVuY3Rpb24gcnVuIChvcHRpb25zOiBDTElPcHRpb25zKTogbnVtYmVyIHtcblx0Y29uc3QgdHNjb25maWdQYXRoID0gZmluZFRzQ29uZmlnKG9wdGlvbnMucHJvamVjdCk7XG5cblx0aWYgKCF0c2NvbmZpZ1BhdGgpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjogQ291bGQgbm90IGZpbmQgdHNjb25maWcuanNvbicpO1xuXHRcdHByb2Nlc3MuZXhpdCgxKTtcblx0fVxuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgVXNpbmcgdHNjb25maWc6ICR7dHNjb25maWdQYXRofWApO1xuXHR9XG5cblx0Ly8gRnJhbWV3b3JrIHZvY2FidWxhcnkgYXJyaXZlcyB2aWEgcGx1Z2lucyDigJQgYSBjb25maWcgZmlsZSBuZXh0IHRvIHRoZVxuXHQvLyB0c2NvbmZpZyAob3IgaW4gY3dkKSBhbmQvb3IgcHJvZ3JhbW1hdGljIG9wdGlvbnMuIE5vbmUgbG9hZGVkIG1lYW5zXG5cdC8vIHRoZSBhbmFseXplciBkZXRlY3RzIHplcm8gaW5zdHJ1bWVudGF0aW9uIHBvaW50cy5cblx0Y29uc3QgcGx1Z2lucyA9IGxvYWRUYWN0aWNhUGx1Z2lucyhwYXRoLmRpcm5hbWUocGF0aC5yZXNvbHZlKHRzY29uZmlnUGF0aCkpLCBvcHRpb25zKTtcblxuXHQvLyBMb2FkIFR5cGVTY3JpcHQgcHJvZ3JhbVxuXHRjb25zdCBwcm9ncmFtID0gbG9hZFByb2dyYW0odHNjb25maWdQYXRoKTtcblxuXHQvLyBDcmVhdGUgYW5hbHl6ZXJcblx0Y29uc3QgYW5hbHl6ZXIgPSBuZXcgTW5lbW9uaWNhQW5hbHl6ZXIocHJvZ3JhbSwgcGx1Z2lucyk7XG5cblx0Ly8gRGV0ZXJtaW5lIG91dHB1dCBkaXJlY3RvcnkgZm9yIGV4Y2x1c2lvblxuXHRjb25zdCBvdXRwdXREaXIgPSBvcHRpb25zLm91dHB1dERpciB8fCAnLnRhY3RpY2EnO1xuXHRjb25zdCBvdXRwdXREaXJQYXRoID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIG91dHB1dERpcik7XG5cdC8vIFRoZSBwcm9qZWN0LWNvbnZlbnRpb25hbCAudGFjdGljYSBkaXIgKG5leHQgdG8gdHNjb25maWcpIGlzIEFMV0FZU1xuXHQvLyBleGNsdWRlZCwgZXZlbiB3aGVuIC0tb3V0cHV0IHBvaW50cyBlbHNld2hlcmU6IGdlbmVyYXRlZCBmaWxlcyBhcmVcblx0Ly8gbmV2ZXIgcHJvamVjdCBzb3VyY2UuIHJlc29sdmUoKSBib3RoIHNpZGVzIOKAlCB0c2NvbmZpZ1BhdGggbWF5IGJlXG5cdC8vIHJlbGF0aXZlICgnLi90c2NvbmZpZy5qc29uJykgd2hpbGUgc291cmNlRmlsZS5maWxlTmFtZSBpcyBhYnNvbHV0ZVxuXHRjb25zdCBjb252ZW50aW9uYWxPdXRwdXREaXIgPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCksICcudGFjdGljYScpO1xuXG5cdC8vIENvbGxlY3Qgc291cmNlIGZpbGVzIHRvIGFuYWx5emVcblx0Y29uc3Qgc291cmNlRmlsZXM6IHRzLlNvdXJjZUZpbGVbXSA9IFtdO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2YgcHJvZ3JhbS5nZXRTb3VyY2VGaWxlcygpKSB7XG5cdFx0aWYgKHNvdXJjZUZpbGUuaXNEZWNsYXJhdGlvbkZpbGUpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGFic29sdXRlRmlsZU5hbWUgPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgc291cmNlRmlsZS5maWxlTmFtZSk7XG5cdFx0aWYgKGFic29sdXRlRmlsZU5hbWUuc3RhcnRzV2l0aChvdXRwdXREaXJQYXRoICsgcGF0aC5zZXApIHx8XG5cdFx0XHRhYnNvbHV0ZUZpbGVOYW1lLnN0YXJ0c1dpdGgoY29udmVudGlvbmFsT3V0cHV0RGlyICsgcGF0aC5zZXApKSB7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cblx0XHQvLyBDaGVjayBleGNsdWRlIHBhdHRlcm5zXG5cdFx0aWYgKG9wdGlvbnMuZXhjbHVkZSkge1xuXHRcdFx0Y29uc3Qgc2hvdWxkRXhjbHVkZSA9IG9wdGlvbnMuZXhjbHVkZS5zb21lKHBhdHRlcm4gPT5cblx0XHRcdFx0c291cmNlRmlsZS5maWxlTmFtZS5pbmNsdWRlcyhwYXR0ZXJuLnJlcGxhY2UoL1xcKi9nLCAnJykpKTtcblx0XHRcdGlmIChzaG91bGRFeGNsdWRlKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIENoZWNrIGluY2x1ZGUgcGF0dGVybnNcblx0XHRpZiAob3B0aW9ucy5pbmNsdWRlICYmIG9wdGlvbnMuaW5jbHVkZS5sZW5ndGggPiAwKSB7XG5cdFx0XHRjb25zdCBzaG91bGRJbmNsdWRlID0gb3B0aW9ucy5pbmNsdWRlLnNvbWUocGF0dGVybiA9PlxuXHRcdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLmluY2x1ZGVzKHBhdHRlcm4ucmVwbGFjZSgvXFwqL2csICcnKSkpO1xuXHRcdFx0aWYgKCFzaG91bGRJbmNsdWRlKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHNvdXJjZUZpbGVzLnB1c2goc291cmNlRmlsZSk7XG5cdH1cblxuXHQvLyBTY2FuIGZvciB0b3BvbG9naWNhIGRpcmVjdG9yeSBzdHJ1Y3R1cmVzIEZJUlNUXG5cdGNvbnN0IHByb2plY3REaXIgPSBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKTtcblx0Y29uc3QgdG9wb2xvZ2ljYURpcnMgPSBzY2FuVG9wb2xvZ2ljYURpcmVjdG9yaWVzKHByb2plY3REaXIsIG9wdGlvbnMudG9wb2xvZ2ljYURpcnMpO1xuXG5cdGlmICh0b3BvbG9naWNhRGlycy5sZW5ndGggPiAwICYmIG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBGb3VuZCB0b3BvbG9naWNhIGRpcmVjdG9yaWVzOiAke3RvcG9sb2dpY2FEaXJzLmpvaW4oJywgJyl9YCk7XG5cdH1cblxuXHQvLyBBbmFseXplIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXMgQkVGT1JFIHVzYWdlIGNvbGxlY3Rpb25cblx0Y29uc3QgdG9wb2xvZ2ljYUFuYWx5emVyID0gbmV3IFRvcG9sb2dpY2FBbmFseXplcigpO1xuXHRjb25zdCB0b3BvbG9naWNhVHlwZXMgPSBuZXcgTWFwPHN0cmluZywgaW1wb3J0KCcuL3R5cGVzJykuVHlwZU5vZGU+KCk7XG5cdGZvciAoY29uc3QgZGlyIG9mIHRvcG9sb2dpY2FEaXJzKSB7XG5cdFx0Y29uc3QgcmVzdWx0ID0gdG9wb2xvZ2ljYUFuYWx5emVyLmFuYWx5emVEaXJlY3RvcnkoZGlyKTtcblx0XHRpZiAocmVzdWx0LnR5cGVzLnNpemUgPiAwKSB7XG5cdFx0XHQvLyBDb2xsZWN0IHRvcG9sb2dpY2EgdHlwZXMgZm9yIGRlZmluaXRpb25zIGFuZCB1c2FnZSB0cmFja2luZ1xuXHRcdFx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBub2RlIF0gb2YgcmVzdWx0LnR5cGVzKSB7XG5cdFx0XHRcdHRvcG9sb2dpY2FUeXBlcy5zZXQodHlwZVBhdGgsIG5vZGUpO1xuXHRcdFx0fVxuXHRcdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0XHRjb25zb2xlLmxvZyhgQWRkZWQgJHtyZXN1bHQudHlwZXMuc2l6ZX0gdHlwZXMgZnJvbSAke2Rpcn1gKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKHJlc3VsdC5lcnJvcnMubGVuZ3RoID4gMCAmJiBvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdHJlc3VsdC5lcnJvcnMuZm9yRWFjaChlcnIgPT4gY29uc29sZS53YXJuKGBbVG9wb2xvZ2ljYV0gJHtlcnJ9YCkpO1xuXHRcdH1cblx0fVxuXG5cdC8vIEFkZCB0b3BvbG9naWNhIHR5cGVzIHRvIGFuYWx5emVyIHNvIHRoZXkncmUgYXZhaWxhYmxlIGZvciB1c2FnZSBkZXRlY3Rpb25cblx0Ly8gUHJvY2VzcyBpbiBvcmRlciBvZiBwYXRoIGRlcHRoIChwYXJlbnRzIGZpcnN0KSB0byBlbnN1cmUgcHJvcGVyIGhpZXJhcmNoeVxuXHRjb25zdCBzb3J0ZWRUeXBlcyA9IEFycmF5LmZyb20odG9wb2xvZ2ljYVR5cGVzLmVudHJpZXMoKSkuc29ydCgoYSwgYikgPT4ge1xuXHRcdGNvbnN0IGRlcHRoQSA9IChhWyAwIF0ubWF0Y2goL1xcLi9nKSB8fCBbXSkubGVuZ3RoO1xuXHRcdGNvbnN0IGRlcHRoQiA9IChiWyAwIF0ubWF0Y2goL1xcLi9nKSB8fCBbXSkubGVuZ3RoO1xuXHRcdHJldHVybiBkZXB0aEEgLSBkZXB0aEI7XG5cdH0pO1xuXHRmb3IgKGNvbnN0IFsgdHlwZVBhdGgsIG5vZGUgXSBvZiBzb3J0ZWRUeXBlcykge1xuXHRcdGFuYWx5emVyLmFkZFRvcG9sb2dpY2FUeXBlKHR5cGVQYXRoLCBub2RlKTtcblx0fVxuXG5cdC8vIEZpcnN0IHBhc3M6IGNvbGxlY3QgYWxsIGRlZmluaXRpb25zLlxuXHQvLyBNb2R1bGUtc2NvcGUgdHJhY2tpbmcgKGltcG9ydHMvZXhwb3J0cyBmb3IgbW9kdWxlcy5qc29uKSBoYXBwZW5zIGluIHRoZVxuXHQvLyBzYW1lIHBhc3Mg4oCUIGl0IG5lZWRzIG9ubHkgdGhlIEFTVCwgbm90IHRoZSBjb2xsZWN0ZWQgZGVmaW5pdGlvbnMuXG5cdGNvbnN0IG1vZHVsZUdyYXBoQnVpbGRlciA9IG5ldyBNb2R1bGVHcmFwaEJ1aWxkZXIocHJvZ3JhbSk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBBbmFseXppbmcgKGRlZmluaXRpb25zKTogJHtzb3VyY2VGaWxlLmZpbGVOYW1lfWApO1xuXHRcdH1cblxuXHRcdHRyeSB7XG5cdFx0XHRhbmFseXplci5hbmFseXplRmlsZShzb3VyY2VGaWxlKTtcblx0XHRcdG1vZHVsZUdyYXBoQnVpbGRlci5hZGRGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdH0gY2F0Y2ggKGVycikge1xuXHRcdFx0Y29uc29sZS5lcnJvcihgRXJyb3IgYW5hbHl6aW5nICR7c291cmNlRmlsZS5maWxlTmFtZX06YCwgZXJyKTtcblx0XHRcdHRocm93IGVycjtcblx0XHR9XG5cdH1cblxuXHQvLyBTZWNvbmQgcGFzczogY29sbGVjdCB1c2FnZXMgKG5vdyBhbGwgZGVmaW5pdGlvbnMgYXJlIGtub3duLCBpbmNsdWRpbmcgdG9wb2xvZ2ljYSlcblx0YW5hbHl6ZXIucmVzZXRVc2FnZXMoKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEFuYWx5emluZyAodXNhZ2VzKTogJHtzb3VyY2VGaWxlLmZpbGVOYW1lfWApO1xuXHRcdH1cblxuXHRcdHRyeSB7XG5cdFx0XHRhbmFseXplci5hbmFseXplRmlsZShzb3VyY2VGaWxlKTtcblx0XHR9IGNhdGNoIChlcnIpIHtcblx0XHRcdGNvbnNvbGUuZXJyb3IoYEVycm9yIGFuYWx5emluZyAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OmAsIGVycik7XG5cdFx0XHR0aHJvdyBlcnI7XG5cdFx0fVxuXHR9XG5cblx0Ly8gR2VuZXJhdGUgdHlwZXMgZnJvbSBtbmVtb25pY2EgYW5hbHlzaXNcblx0Ly8gTm90ZTogdG9wb2xvZ2ljYSB0eXBlcyBhcmUgYWxyZWFkeSBhZGRlZCB0byB0aGUgYW5hbHl6ZXIncyBncmFwaCB2aWEgYWRkVG9wb2xvZ2ljYVR5cGUoKVxuXHRjb25zdCBncmFwaCA9IGFuYWx5emVyLmdldEdyYXBoKCk7XG5cblx0Ly8gUGF0aC1hd2FyZSBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvbiAoaWRlbnRpdHkgbGF3KTogdGhlIGdlbmVyYXRvclxuXHQvLyByZXNvbHZlcyBuYW1lcyB0aHJvdWdoIHRoZSBzYW1lIHJlbGF0aXZlLWZpcnN0L3Jvb3QvdW5pcXVlIHRpZXJzIHRoZVxuXHQvLyBhbmFseXplciB1c2VzOyB0aGUgYW5hbHl6ZXIncyBvd24gdmFsdWUvaW1wb3J0IHRpZXJzIGFscmVhZHkgdmV0dGVkIHRoZVxuXHQvLyB0eXBlIHN0cmluZ3MgZHVyaW5nIGV4dHJhY3Rpb25cblx0Y29uc3QgcmVmZXJlbmNlUmVzb2x2ZXI6IEdyYXBoUmVmZXJlbmNlUmVzb2x2ZXIgPSAoc2ltcGxlTmFtZSwgYW5jaG9yKSA9PiB7XG5cdFx0Y29uc3QgcmVmUmVzdWx0ID0gcmVzb2x2ZUdyYXBoVHlwZVJlZmVyZW5jZShncmFwaCwgc2ltcGxlTmFtZSwgYW5jaG9yKTtcblx0XHRpZiAocmVmUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdHJldHVybiByZWZSZXN1bHQubm9kZTtcblx0XHR9XG5cdFx0aWYgKHJlZlJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRyZXR1cm4gJ2FtYmlndW91cyc7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH07XG5cdGNvbnN0IGdlbmVyYXRvciA9IG5ldyBUeXBlc0dlbmVyYXRvcihncmFwaCwgb3B0aW9ucy5lc20sIG9wdGlvbnMub3V0cHV0RGlyLCByZWZlcmVuY2VSZXNvbHZlcik7XG5cblx0Ly8gQ2hlY2sgaWYgbW9kdWxlIGF1Z21lbnRhdGlvbiBtb2RlIGlzIHJlcXVlc3RlZCAobGVnYWN5KVxuXHRjb25zdCB1c2VNb2R1bGVBdWdtZW50YXRpb24gPSBvcHRpb25zLmdsb2JhbEF1Z21lbnRhdGlvbiA9PT0gZmFsc2U7XG5cblx0Ly8gR2VuZXJhdGUgZXZlcnl0aGluZyBpbnRvIG1lbW9yeSBGSVJTVCDigJQgdGhlIGhhcmQtZmFpbCBsYXcgYmVsb3cgbWF5XG5cdC8vIGFib3J0IHRoZSBydW4sIGFuZCBubyAudGFjdGljYSBvdXRwdXQgYXQgYWxsIG1heSBiZSB3cml0dGVuIHRoZW5cblx0bGV0IGdlbmVyYXRlZFR5cGVzOiB7IGNvbnRlbnQ6IHN0cmluZzsgdHlwZXM6IHN0cmluZ1tdIH07XG5cdGxldCByZWdpc3RyeVR5cGVzOiB7IGNvbnRlbnQ6IHN0cmluZzsgdHlwZXM6IHN0cmluZ1tdIH0gfCB1bmRlZmluZWQ7XG5cdGxldCBvdXRwdXRQYXRoOiBzdHJpbmc7XG5cblx0aWYgKHVzZU1vZHVsZUF1Z21lbnRhdGlvbikge1xuXHRcdC8vIExlZ2FjeSBtb2RlOiBnZW5lcmF0ZSBnbG9iYWwgYXVnbWVudGF0aW9uIGZpbGUgKGluZGV4LmQudHMpXG5cdFx0Z2VuZXJhdGVkVHlwZXMgPSBnZW5lcmF0b3IuZ2VuZXJhdGVHbG9iYWxBdWdtZW50YXRpb24oKTtcblx0fSBlbHNlIHtcblx0XHQvLyBEZWZhdWx0IG1vZGU6IGdlbmVyYXRlIHR5cGVzLnRzIGZvciBtYW51YWwgaW1wb3J0c1xuXHRcdGdlbmVyYXRlZFR5cGVzID0gZ2VuZXJhdG9yLmdlbmVyYXRlVHlwZXNGaWxlKCk7XG5cblx0XHQvLyBHZW5lcmF0ZSByZWdpc3RyeS50cyBmb3IgdHlwZS1zYWZlIGxvb2t1cCgpIGZ1bmN0aW9uXG5cdFx0cmVnaXN0cnlUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZVR5cGVSZWdpc3RyeSgpO1xuXHR9XG5cblx0Ly8gSEFSRCBGQUlMIChncmFwaCBpZGVudGl0eSBsYXcpOiBzYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgbW5lbW9uaWNhXG5cdC8vIGRlZmluaXRpb25zLCBwbHVzIGdyYXBoIHJlZmVyZW5jZXMgdGhhdCBzdGF5IGFtYmlndW91cyBhZnRlclxuXHQvLyBwYXRoLWF3YXJlIHJlc29sdXRpb24gb3IgcmVzb2x2ZSB0byBub3RoaW5nLiBQcmludCBldmVyeSBmYWlsdXJlIHdpdGhcblx0Ly8gYWxsIGl0cyBsb2NhdGlvbnMgYW5kIHdyaXRlIE5PIC50YWN0aWNhIG91dHB1dCBhdCBhbGwuXG5cdGNvbnN0IGZhdGFsRXJyb3JzID0gWyAuLi5hbmFseXplci5nZXRSZXNvbHV0aW9uRXJyb3JzKCksIC4uLmdlbmVyYXRvci5nZXRSZXNvbHV0aW9uRXJyb3JzKCkgXTtcblx0aWYgKGZhdGFsRXJyb3JzLmxlbmd0aCA+IDApIHtcblx0XHRjb25zdCBzZWVuID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0bGV0IHByaW50ZWQgPSAwO1xuXHRcdGZvciAoY29uc3QgZXJyb3Igb2YgZmF0YWxFcnJvcnMpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke2Vycm9yLm1lc3NhZ2V9fCR7ZXJyb3IubG9jYXRpb25zLmpvaW4oJ3wnKX1gO1xuXHRcdFx0aWYgKHNlZW4uaGFzKGtleSkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRzZWVuLmFkZChrZXkpO1xuXHRcdFx0cHJpbnRlZCsrO1xuXHRcdFx0Y29uc29sZS5lcnJvcihgdGFjdGljYTogJHtlcnJvci5tZXNzYWdlfWApO1xuXHRcdFx0Zm9yIChjb25zdCBsb2NhdGlvbiBvZiBlcnJvci5sb2NhdGlvbnMpIHtcblx0XHRcdFx0Y29uc29sZS5lcnJvcihgICBhdCAke2xvY2F0aW9ufWApO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zb2xlLmVycm9yKGB0YWN0aWNhOiBhYm9ydGluZyDigJQgJHtwcmludGVkfSByZXNvbHV0aW9uIGZhaWx1cmUocyk7IG5vIC50YWN0aWNhIG91dHB1dCB3cml0dGVuYCk7XG5cdFx0cmV0dXJuIDE7XG5cdH1cblxuXHRjb25zdCB3cml0ZXIgPSBuZXcgVHlwZXNXcml0ZXIob3B0aW9ucy5vdXRwdXREaXIpO1xuXG5cdGlmICh1c2VNb2R1bGVBdWdtZW50YXRpb24pIHtcblx0XHQvLyBMZWdhY3kgbW9kZTogd3JpdGUgZ2xvYmFsIGF1Z21lbnRhdGlvbiBmaWxlIChpbmRleC5kLnRzKVxuXHRcdG91dHB1dFBhdGggPSB3cml0ZXIud3JpdGVHbG9iYWxBdWdtZW50YXRpb24oZ2VuZXJhdGVkVHlwZXMpO1xuXHR9IGVsc2Uge1xuXHRcdC8vIERlZmF1bHQgbW9kZTogd3JpdGUgdHlwZXMudHMgZm9yIG1hbnVhbCBpbXBvcnRzXG5cdFx0b3V0cHV0UGF0aCA9IHdyaXRlci53cml0ZVR5cGVzRmlsZShnZW5lcmF0ZWRUeXBlcyk7XG5cblx0XHRjb25zdCByZWdpc3RyeVBhdGggPSB3cml0ZXIud3JpdGVUbygncmVnaXN0cnkudHMnLCByZWdpc3RyeVR5cGVzIS5jb250ZW50KTtcblxuXHRcdC8vIEdlbmVyYXRlIGluZGV4LnRzIHRvIGV4cG9ydCBldmVyeXRoaW5nXG5cdFx0Y29uc3QgaW5kZXhDb250ZW50ID0gYC8vIEdlbmVyYXRlZCBieSBAbW5lbW9uaWNhL3RhY3RpY2EgLSBETyBOT1QgRURJVFxuLy8gRXhwb3J0IGFsbCBnZW5lcmF0ZWQgdHlwZXNcblxuZXhwb3J0ICogZnJvbSAnLi90eXBlcyR7b3B0aW9ucy5lc20gPyAnLmpzJyA6ICcnfSc7XG5leHBvcnQgKiBmcm9tICcuL3JlZ2lzdHJ5JHtvcHRpb25zLmVzbSA/ICcuanMnIDogJyd9JztcbmA7XG5cdFx0d3JpdGVyLndyaXRlVG8oJ2luZGV4LnRzJywgaW5kZXhDb250ZW50KTtcblxuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgcmVnaXN0cnkudHMgYXQ6ICR7cmVnaXN0cnlQYXRofWApO1xuXHRcdH1cblx0fVxuXG5cdC8vIEdlbmVyYXRlIGRlZmluaXRpb25zLmpzb24gYW5kIHVzYWdlcy5qc29uIGZvciBjb2RlIG5hdmlnYXRpb25cblx0Ly8gSW5jbHVkZSBib3RoIG1uZW1vbmljYSBhbmQgdG9wb2xvZ2ljYSBkZWZpbml0aW9uc1xuXHRjb25zdCBkZWZpbml0aW9ucyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0RGVmaW5pdGlvbnMoKSk7XG5cdGNvbnN0IHVzYWdlcyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0VXNhZ2VzKCkpO1xuXHRcblx0Ly8gQWRkIHRvcG9sb2dpY2EgdHlwZXMgdG8gZGVmaW5pdGlvbnNcblx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCB0eXBlTm9kZSBdIG9mIHRvcG9sb2dpY2FUeXBlcykge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHMgKHByZWZlciBtbmVtb25pY2EncyBhbmFseXNpcylcblx0XHRpZiAoZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXHRcdFxuXHRcdGNvbnN0IGRlZmluaXRpb246IGltcG9ydCgnLi90eXBlcycpLkRlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTm9kZS5uYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHt0eXBlTm9kZS5zb3VyY2VGaWxlfToke3R5cGVOb2RlLmxpbmV9OiR7dHlwZU5vZGUuY29sdW1ufWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiB0eXBlTm9kZS5wYXJlbnQgPyB0eXBlTm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0ZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0fVxuXG5cdC8vIExvY2FsLXNjb3BlIHdhbGsgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgUGhhc2UgMik6IGZ1bmN0aW9uL21ldGhvZC9hcnJvd1xuXHQvLyBzY29wZXMgb25seSAobm8gYmxvY2sgc2NvcGVzIOKAlCBkZWNpc2lvbiA1KSwgdmFyaWFibGVzIHdpdGggaXNNdXRhYmxlIGFuZFxuXHQvLyByZWFzc2lnbm1lbnQgc2l0ZXMgKGRlY2lzaW9uIDYpLiBSdW5zIGFmdGVyIGRlZmluaXRpb25zIGFyZSBrbm93biBzb1xuXHQvLyB2YXJpYWJsZSB0eXBlUGF0aHMgY2FuIHJlc29sdmU7IGhvbGRlclNjb3BlSWQgaXMgYXR0YWNoZWQgdG8gdXNhZ2VzXG5cdC8vIGJlZm9yZSB0aGV5IGFyZSB3cml0dGVuLlxuXHRjb25zdCBzY29wZVdhbGtlciA9IG5ldyBMb2NhbFNjb3BlV2Fsa2VyKCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdHNjb3BlV2Fsa2VyLmFkZEZpbGUoc291cmNlRmlsZSk7XG5cdH1cblx0Y29uc3Qgc2NvcGVSZXNvbHZlcjogU2NvcGVUeXBlUmVzb2x2ZXIgPSB7XG5cdFx0cmVzb2x2ZUJ5TmFtZSA6IChuYW1lOiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQgPT4ge1xuXHRcdFx0aWYgKGRlZmluaXRpb25zLmhhcyhuYW1lKSkge1xuXHRcdFx0XHRyZXR1cm4gbmFtZTtcblx0XHRcdH1cblx0XHRcdGxldCBmb3VuZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdFx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCBkZWZpbml0aW9uIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRcdFx0aWYgKGRlZmluaXRpb24ubmFtZSAhPT0gbmFtZSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdC8vIEFtYmlndW91cyBuYW1lIOKAlCBubyB0eXBlIGNoZWNrZXIsIHNvIHJlZnVzZSB0byBndWVzc1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Zm91bmQgPSBmdWxsUGF0aDtcblx0XHRcdH1cblx0XHRcdHJldHVybiBmb3VuZDtcblx0XHR9LFxuXHRcdGhhc1BhdGggOiAoZnVsbFBhdGg6IHN0cmluZyk6IGJvb2xlYW4gPT4ge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fSxcblx0XHQvLyBUaGUgYW5hbHl6ZXIncyBvd24gbG9va3VwIGxhdywgYWdhaW5zdCB0aGUgc2FtZSBjb21wbGV0ZSBncmFwaCB0aGVcblx0XHQvLyB1c2FnZXMgcGFzcyByZXNvbHZlZCB3aXRoIOKAlCBhIGxvb2t1cCgpIGluaXRpYWxpemVyIHRoZSBhbmFseXplclxuXHRcdC8vIGFjY2VwdGVkIChlLmcuIGFuIGltcG9ydGVkIEhvbGRlci5sb29rdXAoJ1Rva2VuJykpIGxhbmRzIHRoZSBzYW1lXG5cdFx0Ly8gZnVsbFBhdGggaW4gc2NvcGVzLmpzb24gaW5zdGVhZCBvZiBzdGFydmluZyB0aGUgY3JlYXRpb24tZ3JhcGhcblx0XHQvLyBhbmNob3JzLiBSZWplY3RlZCBsb29rdXBzIHN0YXkgdHlwZVBhdGgtbGVzcyBoZXJlOyB0aGUgYW5hbHl6ZXJcblx0XHQvLyBhbHJlYWR5IGhhcmQtZmFpbGVkIHRoZSBydW4gYWJvdmUuXG5cdFx0cmVzb2x2ZUxvb2t1cCA6IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCA9PiB7XG5cdFx0XHRjb25zdCByZXNvbHZlZCA9IGFuYWx5emVyLnJlc29sdmVMb29rdXBDYWxsUGF0aChjYWxsKTtcblx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHR9LFxuXHR9O1xuXHRjb25zdCBzY29wZUFuYWx5c2lzID0gc2NvcGVXYWxrZXIuYnVpbGQoc2NvcGVSZXNvbHZlcik7XG5cdExvY2FsU2NvcGVXYWxrZXIuYXR0YWNoSG9sZGVyU2NvcGVJZHModXNhZ2VzLCBzY29wZVdhbGtlcik7XG5cblx0Y29uc3QgZGVmaW5pdGlvbnNQYXRoID0gd3JpdGVyLndyaXRlRGVmaW5pdGlvbnNGaWxlKGRlZmluaXRpb25zKTtcblx0Y29uc3QgdXNhZ2VzUGF0aCA9IHdyaXRlci53cml0ZVVzYWdlc0ZpbGUodXNhZ2VzKTtcblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBkZWZpbml0aW9ucy5qc29uIGF0OiAke2RlZmluaXRpb25zUGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHVzYWdlcy5qc29uIGF0OiAke3VzYWdlc1BhdGh9YCk7XG5cdH1cblxuXHQvLyBEZXRlcm1pbmUgRURTIHNldHRpbmc6IGV4cGxpY2l0IGZsYWcgPiBhdXRvLWRldGVjdCBkaXZlID4gZGVmYXVsdCBvZmZcblx0bGV0IGVuYWJsZUVEUyA9IG9wdGlvbnMuZWRzO1xuXHRpZiAoZW5hYmxlRURTID09PSB1bmRlZmluZWQpIHtcblx0XHRlbmFibGVFRFMgPSBoYXNEaXZlRGVwZW5kZW5jeShwcm9qZWN0RGlyKTtcblx0fVxuXG5cdGlmIChlbmFibGVFRFMpIHtcblx0XHRjb25zdCBlZHMgPSBhbmFseXplci5nZXRFRFNVc2FnZXMoKTtcblx0XHRhdHRhY2hXcmFwSm9pbkRhdGEoZWRzLCBzY29wZVdhbGtlciwgc2NvcGVBbmFseXNpcyk7XG5cdFx0Y29uc3QgZWRzUGF0aCA9IHdyaXRlci53cml0ZUVEU0ZpbGUoZWRzKTtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGVkcy5qc29uIGF0OiAke2Vkc1BhdGh9YCk7XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIGZsb3cuanNvbiAobmF0aXZlIGluc3RhbmNlIHVzYWdlIHRyYWNraW5nKVxuXHRjb25zdCBmbG93ID0gYW5hbHl6ZXIuZ2V0Rmxvd1VzYWdlcygpO1xuXHRjb25zdCBmbG93UGF0aCA9IHdyaXRlci53cml0ZUZsb3dGaWxlKGZsb3cpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3QgZmxvd0NvdW50ID0gQXJyYXkuZnJvbShmbG93LnZhbHVlcygpKS5yZWR1Y2UoKHN1bSwgYXJyKSA9PiBzdW0gKyBhcnIubGVuZ3RoLCAwKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGZsb3cuanNvbiBhdDogJHtmbG93UGF0aH0gKCR7Zmxvd0NvdW50fSBmbG93IGVudHJpZXMpYCk7XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgbW9kdWxlcy5qc29uIChtb2R1bGUtc2NvcGUgZ3JhcGg6IGltcG9ydHMvZXhwb3J0cyxcblx0Ly8gZGVwZW5kZW5jaWVzLCBjeWNsZXMsIGNyb3NzLW1vZHVsZSBtbmVtb25pY2EtdHlwZSBlZGdlcylcblx0Y29uc3QgZGVmaW5lZFR5cGVzQnlGaWxlID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZ1tdPigpO1xuXHRmb3IgKGNvbnN0IFsgZnVsbFBhdGgsIGRlZmluaXRpb24gXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdGNvbnN0IHsgbG9jYXRpb24gfSA9IGRlZmluaXRpb247XG5cdFx0Y29uc3QgbGFzdENvbG9uID0gbG9jYXRpb24ubGFzdEluZGV4T2YoJzonKTtcblx0XHRjb25zdCBwcmV2Q29sb24gPSBsb2NhdGlvbi5sYXN0SW5kZXhPZignOicsIGxhc3RDb2xvbiAtIDEpO1xuXHRcdGNvbnN0IGZpbGUgPSBsb2NhdGlvbi5zbGljZSgwLCBwcmV2Q29sb24pO1xuXHRcdGNvbnN0IGxpc3QgPSBkZWZpbmVkVHlwZXNCeUZpbGUuZ2V0KGZpbGUpID8/IFtdO1xuXHRcdGxpc3QucHVzaChmdWxsUGF0aCk7XG5cdFx0ZGVmaW5lZFR5cGVzQnlGaWxlLnNldChmaWxlLCBsaXN0KTtcblx0fVxuXHRjb25zdCBtb2R1bGVHcmFwaCA9IG1vZHVsZUdyYXBoQnVpbGRlci5idWlsZChkZWZpbmVkVHlwZXNCeUZpbGUpO1xuXHRjb25zdCBtb2R1bGVzUGF0aCA9IHdyaXRlci53cml0ZU1vZHVsZXNGaWxlKG1vZHVsZUdyYXBoKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IG1vZHVsZUNvdW50ID0gbW9kdWxlR3JhcGgubW9kdWxlcy5zaXplO1xuXHRcdGNvbnN0IGVkZ2VDb3VudCA9IG1vZHVsZUdyYXBoLmVkZ2VzLmxlbmd0aDtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIG1vZHVsZXMuanNvbiBhdDogJHttb2R1bGVzUGF0aH0gKCR7bW9kdWxlQ291bnR9IG1vZHVsZXMsICR7ZWRnZUNvdW50fSBlZGdlcylgKTtcblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBzY29wZXMuanNvbiAobG9jYWwtc2NvcGUgd2Fsa2VyOiBzY29wZXMsIHZhcmlhYmxlcyxcblx0Ly8gcmVhc3NpZ25tZW50IGZsb3ctdGVybWluYXRpb24gcG9pbnRzKVxuXHRjb25zdCBzY29wZXNQYXRoID0gd3JpdGVyLndyaXRlU2NvcGVzRmlsZShzY29wZUFuYWx5c2lzKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IHNjb3BlQ291bnQgPSBzY29wZUFuYWx5c2lzLnNjb3Blcy5zaXplO1xuXHRcdGNvbnN0IHZhcmlhYmxlQ291bnQgPSBzY29wZUFuYWx5c2lzLnZhcmlhYmxlcy5zaXplO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgc2NvcGVzLmpzb24gYXQ6ICR7c2NvcGVzUGF0aH0gKCR7c2NvcGVDb3VudH0gc2NvcGVzLCAke3ZhcmlhYmxlQ291bnR9IHZhcmlhYmxlcylgKTtcblx0fVxuXG5cdC8vIFRoZSBpbnNpZGUtb3V0IGNyZWF0aW9uIHdhbGsgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgUGhhc2UgMyk6IGFuY2hvcnNcblx0Ly8gYXJlIHRoZSBpbnN0YW50aWF0aW9uIHVzYWdlczsgY2FsbGVycyBhcmUgZm9sbG93ZWQgc2FtZS1maWxlIGFuZFxuXHQvLyBjcm9zcy1maWxlIChtb2R1bGUgZ3JhcGgsIGJhcnJlbHMgY2hhc2VkKSB1bnRpbCBvbmx5IHN0YXJ0ZXJzIHJlbWFpbi5cblx0Y29uc3Qgc291cmNlRmlsZXNCeVBhdGggPSBuZXcgTWFwPHN0cmluZywgdHMuU291cmNlRmlsZT4oKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0c291cmNlRmlsZXNCeVBhdGguc2V0KHBhdGgucmVzb2x2ZShzb3VyY2VGaWxlLmZpbGVOYW1lKSwgc291cmNlRmlsZSk7XG5cdH1cblx0Y29uc3QgY3JlYXRpb25HcmFwaEJ1aWxkZXIgPSBuZXcgQ3JlYXRpb25HcmFwaEJ1aWxkZXIobW9kdWxlR3JhcGgsIHNjb3BlQW5hbHlzaXMsIHNjb3BlV2Fsa2VyLCBzb3VyY2VGaWxlc0J5UGF0aCk7XG5cdGNvbnN0IGNyZWF0aW9uR3JhcGggPSBjcmVhdGlvbkdyYXBoQnVpbGRlci5idWlsZCh1c2FnZXMpO1xuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBpbnN0cnVtZW50YXRpb24uanNvbiAoZnJhbWV3b3JrIGxpZmVjeWNsZSBjcm9zc3JvYWRzXG5cdC8vIGZyb20gdGhlIGxvYWRlZCBwbHVnaW5zIOKAlCBzeW50YWN0aWMgZGV0ZWN0aW9uIG5lZWRzIG5vIGRpdmVcblx0Ly8gZGVwZW5kZW5jeSwgdW5saWtlIGVkcy5qc29uKS4gdjIgY2FycmllcyB0aGUgY3JlYXRpb24gZ3JhcGhcblx0Ly8gYWxvbmdzaWRlIHRoZSBwb2ludHMuXG5cdGNvbnN0IGluc3RydW1lbnRhdGlvbiA9IGFuYWx5emVyLmdldEluc3RydW1lbnRhdGlvblBvaW50cygpO1xuXHRjb25zdCBpbnN0cnVtZW50YXRpb25QYXRoID0gd3JpdGVyLndyaXRlSW5zdHJ1bWVudGF0aW9uRmlsZShpbnN0cnVtZW50YXRpb24sIGNyZWF0aW9uR3JhcGgpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3Qgbm9kZUNvdW50ID0gY3JlYXRpb25HcmFwaC5ub2Rlcy5sZW5ndGg7XG5cdFx0Y29uc3QgZWRnZUNvdW50ID0gY3JlYXRpb25HcmFwaC5lZGdlcy5sZW5ndGg7XG5cdFx0Y29uc3QgYW5jaG9yQ291bnQgPSBjcmVhdGlvbkdyYXBoLmFuY2hvcnMubGVuZ3RoO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaW5zdHJ1bWVudGF0aW9uLmpzb24gYXQ6ICR7aW5zdHJ1bWVudGF0aW9uUGF0aH0gKCR7aW5zdHJ1bWVudGF0aW9uLmxlbmd0aH0gcG9pbnRzKWApO1xuXHRcdGNvbnNvbGUubG9nKGAgIGNyZWF0aW9uIGdyYXBoOiAke25vZGVDb3VudH0gbm9kZXMsICR7ZWRnZUNvdW50fSBlZGdlcywgJHthbmNob3JDb3VudH0gYW5jaG9yc2ApO1xuXHR9XG5cblx0Ly8gR2VuZXJhdGUgaGllcmFyY2h5Lmpzb24gKHN0cnVjdHVyZWQpIGFuZCBoaWVyYXJjaHkudHh0IChBU0NJSSB0cmVlKSBmb3IgdGhlIFRyaWVcblx0Y29uc3QgaGllcmFyY2h5Um9vdHMgPSBncmFwaC50b0hpZXJhcmNoeSgpO1xuXHRjb25zdCBoaWVyYXJjaHlKc29uUGF0aCA9IHdyaXRlci53cml0ZUhpZXJhcmNoeUZpbGUoaGllcmFyY2h5Um9vdHMpO1xuXHRjb25zdCBoaWVyYXJjaHlUZXh0ID0gcmVuZGVyVHlwZUhpZXJhcmNoeShncmFwaCk7XG5cdGNvbnN0IGhpZXJhcmNoeVR4dFBhdGggPSB3cml0ZXIud3JpdGVUbygnaGllcmFyY2h5LnR4dCcsIGhpZXJhcmNoeVRleHQpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBoaWVyYXJjaHkuanNvbiBhdDogJHtoaWVyYXJjaHlKc29uUGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGhpZXJhcmNoeS50eHQgYXQ6ICR7aGllcmFyY2h5VHh0UGF0aH1gKTtcblx0fVxuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHR5cGVzIGF0OiAke291dHB1dFBhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coYE1vZGU6ICR7dXNlTW9kdWxlQXVnbWVudGF0aW9uID8gJ2dsb2JhbCBhdWdtZW50YXRpb24gKGxlZ2FjeSknIDogJ3R5cGVzIGZpbGUgKGRlZmF1bHQpJ31gKTtcblx0XHRjb25zb2xlLmxvZyhgRm91bmQgJHtnZW5lcmF0ZWRUeXBlcy50eXBlcy5sZW5ndGh9IHR5cGVzOmApO1xuXHRcdHByaW50VHlwZUhpZXJhcmNoeShncmFwaCk7XG5cdH0gZWxzZSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCAke2dlbmVyYXRlZFR5cGVzLnR5cGVzLmxlbmd0aH0gdHlwZXMgYXQgJHtvcHRpb25zLm91dHB1dERpciB8fCAnLnRhY3RpY2EnfWApO1xuXHRcdGlmICh1c2VNb2R1bGVBdWdtZW50YXRpb24pIHtcblx0XHRcdGNvbnNvbGUubG9nKCdVc2luZyBnbG9iYWwgYXVnbWVudGF0aW9uIG1vZGUgKGxlZ2FjeSwgdXNlIGRlZmF1bHQgbW9kZSBmb3IgdHlwZXMudHMgb25seSknKTtcblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gMDtcbn1cblxuLyoqXG4gKiBXYXRjaCBtb2RlXG4gKi9cbmZ1bmN0aW9uIHdhdGNoIChvcHRpb25zOiBDTElPcHRpb25zKTogdm9pZCB7XG5cdGNvbnNvbGUubG9nKCdTdGFydGluZyB3YXRjaCBtb2RlLi4uJyk7XG5cblx0Ly8gSW5pdGlhbCBydW5cblx0cnVuKG9wdGlvbnMpO1xuXG5cdC8vIFNldCB1cCBmaWxlIHdhdGNoaW5nXG5cdGNvbnN0IGNob2tpZGFyID0gcmVxdWlyZSgnY2hva2lkYXInKTtcblx0Y29uc3QgdHNjb25maWdQYXRoID0gZmluZFRzQ29uZmlnKG9wdGlvbnMucHJvamVjdCk7XG5cblx0aWYgKCF0c2NvbmZpZ1BhdGgpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjogQ291bGQgbm90IGZpbmQgdHNjb25maWcuanNvbicpO1xuXHRcdHByb2Nlc3MuZXhpdCgxKTtcblx0fVxuXG5cdGNvbnN0IHByb2plY3REaXIgPSBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKTtcblx0Y29uc3Qgd2F0Y2hQYXRocyA9IG9wdGlvbnMuaW5jbHVkZSB8fCBbICcqKi8qLnRzJyBdO1xuXHRjb25zdCBpZ25vcmVQYXRocyA9IG9wdGlvbnMuZXhjbHVkZSB8fCBbICcqKi8qLmQudHMnLCAnbm9kZV9tb2R1bGVzLyoqJywgJy50YWN0aWNhLyoqJyBdO1xuXG5cdGNvbnN0IHdhdGNoZXIgPSBjaG9raWRhci53YXRjaCh3YXRjaFBhdGhzLCB7XG5cdFx0Y3dkICAgICAgICA6IHByb2plY3REaXIsXG5cdFx0aWdub3JlZCAgICA6IGlnbm9yZVBhdGhzLFxuXHRcdHBlcnNpc3RlbnQgOiB0cnVlLFxuXHR9KTtcblxuXHR3YXRjaGVyLm9uKCdjaGFuZ2UnLCAoZmlsZVBhdGg6IHN0cmluZykgPT4ge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBGaWxlIGNoYW5nZWQ6ICR7ZmlsZVBhdGh9YCk7XG5cdFx0fVxuXHRcdHJ1bihvcHRpb25zKTtcblx0fSk7XG5cblx0d2F0Y2hlci5vbignYWRkJywgKGZpbGVQYXRoOiBzdHJpbmcpID0+IHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgRmlsZSBhZGRlZDogJHtmaWxlUGF0aH1gKTtcblx0XHR9XG5cdFx0cnVuKG9wdGlvbnMpO1xuXHR9KTtcblxuXHRjb25zb2xlLmxvZygnV2F0Y2hpbmcgZm9yIGNoYW5nZXMuLi4gKFByZXNzIEN0cmwrQyB0byBzdG9wKScpO1xufVxuXG4vKipcbiAqIE1haW4gZW50cnkgcG9pbnRcbiAqL1xuZnVuY3Rpb24gbWFpbiAoKTogdm9pZCB7XG5cdGNvbnN0IGFyZ3MgPSBwcm9jZXNzLmFyZ3Yuc2xpY2UoMik7XG5cdGNvbnN0IG9wdGlvbnMgPSBwYXJzZUFyZ3MoYXJncyk7XG5cblx0aWYgKG9wdGlvbnMuaGVscCkge1xuXHRcdHByaW50SGVscCgpO1xuXHRcdHByb2Nlc3MuZXhpdCgwKTtcblx0fVxuXG5cdHRyeSB7XG5cdFx0aWYgKG9wdGlvbnMud2F0Y2gpIHtcblx0XHRcdHdhdGNoKG9wdGlvbnMpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHRjb25zdCBjb2RlID0gcnVuKG9wdGlvbnMpO1xuXHRcdFx0aWYgKGNvZGUpIHtcblx0XHRcdFx0cHJvY2Vzcy5leGl0KGNvZGUpO1xuXHRcdFx0fVxuXHRcdH1cblx0fSBjYXRjaCAoZXJyb3IpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjonLCBlcnJvciBpbnN0YW5jZW9mIEVycm9yID8gZXJyb3IubWVzc2FnZSA6IGVycm9yKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cbn1cblxuLy8gUnVuIGlmIGV4ZWN1dGVkIGRpcmVjdGx5XG5pZiAocmVxdWlyZS5tYWluID09PSBtb2R1bGUpIHtcblx0bWFpbigpO1xufVxuXG5leHBvcnQge1xuXHRtYWluLCBydW4sIHdhdGNoLCBwYXJzZUFyZ3MgXG59O1xuIl19