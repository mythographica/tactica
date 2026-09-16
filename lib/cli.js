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
    // Project root anchors the relative paths the writer emits: .tactica
    // output must stay portable when the checkout moves between machines.
    // resolve() both sides — tsconfigPath itself may be relative.
    const projectRoot = path.resolve(process.cwd(), path.dirname(tsconfigPath));
    const writer = new writer_1.TypesWriter(options.outputDir, projectRoot);
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQW82Qlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUFsNkI1Qix1Q0FBeUI7QUFDekIsMkNBQTZCO0FBQzdCLG1DQUF1QztBQUN2QywrQ0FBaUM7QUFDakMseUNBQStDO0FBQy9DLCtEQUEyRDtBQUMzRCwyQ0FFcUI7QUFDckIscUNBQXVDO0FBQ3ZDLGlEQUFvRDtBQUNwRCxxREFBd0Q7QUFDeEQscUNBRWtCO0FBQ2xCLG1DQUVpQjtBQTBCakI7O0dBRUc7QUFDSCxTQUFTLFNBQVMsQ0FBRSxJQUFjO0lBQ2pDLE1BQU0sT0FBTyxHQUFlLEVBQUUsQ0FBQztJQUUvQixLQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRSxDQUFDO1FBQ3RDLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBRSxDQUFDLENBQUUsQ0FBQztRQUV0QixRQUFRLEdBQUcsRUFBRSxDQUFDO1lBQ2QsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFNBQVM7Z0JBQ2IsT0FBTyxDQUFDLEtBQUssR0FBRyxJQUFJLENBQUM7Z0JBQ3JCLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssV0FBVztnQkFDZixPQUFPLENBQUMsT0FBTyxHQUFHLElBQUksQ0FBRSxFQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUM5QixNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFVBQVU7Z0JBQ2QsT0FBTyxDQUFDLFNBQVMsR0FBRyxJQUFJLENBQUUsRUFBRSxDQUFDLENBQUUsQ0FBQztnQkFDaEMsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxXQUFX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eEUsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQztJQUNqQixDQUFDO0FBQ0YsQ0FBQztBQUVELDJCQUEyQjtBQUMzQixJQUFJLE9BQU8sQ0FBQyxJQUFJLEtBQUssTUFBTSxFQUFFLENBQUM7SUFDN0IsSUFBSSxFQUFFLENBQUM7QUFDUixDQUFDIiwic291cmNlc0NvbnRlbnQiOlsiIyEvdXNyL2Jpbi9lbnYgbm9kZVxuJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBmcyBmcm9tICdmcyc7XG5pbXBvcnQgKiBhcyBwYXRoIGZyb20gJ3BhdGgnO1xuaW1wb3J0IHsgY3JlYXRlUmVxdWlyZSB9IGZyb20gJ21vZHVsZSc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7IE1uZW1vbmljYUFuYWx5emVyIH0gZnJvbSAnLi9hbmFseXplcic7XG5pbXBvcnQgeyBUb3BvbG9naWNhQW5hbHl6ZXIgfSBmcm9tICcuL3RvcG9sb2dpY2EtYW5hbHl6ZXInO1xuaW1wb3J0IHtcblx0VHlwZXNHZW5lcmF0b3IsIEdyYXBoUmVmZXJlbmNlUmVzb2x2ZXIgXG59IGZyb20gJy4vZ2VuZXJhdG9yJztcbmltcG9ydCB7IFR5cGVzV3JpdGVyIH0gZnJvbSAnLi93cml0ZXInO1xuaW1wb3J0IHsgTW9kdWxlR3JhcGhCdWlsZGVyIH0gZnJvbSAnLi9tb2R1bGUtZ3JhcGgnO1xuaW1wb3J0IHsgQ3JlYXRpb25HcmFwaEJ1aWxkZXIgfSBmcm9tICcuL2NyZWF0aW9uLWdyYXBoJztcbmltcG9ydCB7XG5cdExvY2FsU2NvcGVXYWxrZXIsIFNjb3BlVHlwZVJlc29sdmVyXG59IGZyb20gJy4vc2NvcGVzJztcbmltcG9ydCB7XG5cdHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UsIFR5cGVHcmFwaEltcGwgXG59IGZyb20gJy4vZ3JhcGgnO1xuaW1wb3J0IHtcblx0VGFjdGljYUNvbmZpZywgVHlwZU5vZGUsIEVEU0luZm8sIFNjb3BlQW5hbHlzaXNcbn0gZnJvbSAnLi90eXBlcyc7XG5pbXBvcnQgeyBUYWN0aWNhUGx1Z2luIH0gZnJvbSAnLi9wbHVnaW5zJztcblxuLyoqXG4gKiBDTEkgZW50cnkgcG9pbnQgZm9yIFRhY3RpY2FcbiAqXG4gKiBSdW5zIHRoZSBhbmFseXplciBvdmVyIGEgdHNjb25maWcgcHJvamVjdCBhbmQgd3JpdGVzIC50YWN0aWNhLyBvdXRwdXRcbiAqL1xuXG5pbnRlcmZhY2UgQ0xJT3B0aW9ucyBleHRlbmRzIFRhY3RpY2FDb25maWcge1xuXHR3YXRjaD86IGJvb2xlYW47XG5cdHByb2plY3Q/OiBzdHJpbmc7XG5cdGhlbHA/OiBib29sZWFuO1xuXHQvKiogQ3VzdG9tIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXMgdG8gc2NhbiAqL1xuXHR0b3BvbG9naWNhRGlycz86IHN0cmluZ1tdO1xuXHQvKiogQWRkIC5qcyBleHRlbnNpb25zIHRvIHJlbGF0aXZlIGltcG9ydHMgZm9yIEVTTSBOb2RlTmV4dCByZXNvbHV0aW9uICovXG5cdGVzbT86IGJvb2xlYW47XG5cdC8qKiBFbmFibGUgRURTIChFeGVjdXRpb24gRGF0YSBTdG9yYWdlKSB0cmFja2luZyAqL1xuXHRlZHM/OiBib29sZWFuO1xuXHQvKiogUHJvZ3JhbW1hdGljIHBsdWdpbnM7IGNvbmZpZy1maWxlIHBsdWdpbnMgYXJlIGFwcGVuZGVkIGFmdGVyIHRoZXNlICovXG5cdHBsdWdpbnM/OiBUYWN0aWNhUGx1Z2luW107XG59XG5cbi8qKlxuICogUGFyc2UgY29tbWFuZCBsaW5lIGFyZ3VtZW50c1xuICovXG5mdW5jdGlvbiBwYXJzZUFyZ3MgKGFyZ3M6IHN0cmluZ1tdKTogQ0xJT3B0aW9ucyB7XG5cdGNvbnN0IG9wdGlvbnM6IENMSU9wdGlvbnMgPSB7fTtcblxuXHRmb3IgKGxldCBpID0gMDsgaSA8IGFyZ3MubGVuZ3RoOyBpKyspIHtcblx0XHRjb25zdCBhcmcgPSBhcmdzWyBpIF07XG5cblx0XHRzd2l0Y2ggKGFyZykge1xuXHRcdGNhc2UgJy13Jzpcblx0XHRjYXNlICctLXdhdGNoJzpcblx0XHRcdG9wdGlvbnMud2F0Y2ggPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXAnOlxuXHRcdGNhc2UgJy0tcHJvamVjdCc6XG5cdFx0XHRvcHRpb25zLnByb2plY3QgPSBhcmdzWyArK2kgXTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1vJzpcblx0XHRjYXNlICctLW91dHB1dCc6XG5cdFx0XHRvcHRpb25zLm91dHB1dERpciA9IGFyZ3NbICsraSBdO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLWknOlxuXHRcdGNhc2UgJy0taW5jbHVkZSc6XG5cdFx0XHRvcHRpb25zLmluY2x1ZGUgPSAob3B0aW9ucy5pbmNsdWRlIHx8IFtdKS5jb25jYXQoYXJnc1sgKytpIF0uc3BsaXQoJywnKSk7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctZSc6XG5cdFx0Y2FzZSAnLS1leGNsdWRlJzpcblx0XHRcdG9wdGlvbnMuZXhjbHVkZSA9IChvcHRpb25zLmV4Y2x1ZGUgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1tJzpcblx0XHRjYXNlICctLW1vZHVsZS1hdWdtZW50YXRpb24nOlxuXHRcdFx0b3B0aW9ucy5nbG9iYWxBdWdtZW50YXRpb24gPSBmYWxzZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy12Jzpcblx0XHRjYXNlICctLXZlcmJvc2UnOlxuXHRcdFx0b3B0aW9ucy52ZXJib3NlID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy10Jzpcblx0XHRjYXNlICctLXRvcG9sb2dpY2EnOlxuXHRcdFx0b3B0aW9ucy50b3BvbG9naWNhRGlycyA9IChvcHRpb25zLnRvcG9sb2dpY2FEaXJzIHx8IFtdKS5jb25jYXQoYXJnc1sgKytpIF0uc3BsaXQoJywnKSk7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctLWVzbSc6XG5cdFx0XHRvcHRpb25zLmVzbSA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctLWVkcyc6XG5cdFx0XHRvcHRpb25zLmVkcyA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctLW5vLWVkcyc6XG5cdFx0XHRvcHRpb25zLmVkcyA9IGZhbHNlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLWgnOlxuXHRcdGNhc2UgJy0taGVscCc6XG5cdFx0XHRvcHRpb25zLmhlbHAgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIG9wdGlvbnM7XG59XG5cbi8qKlxuICogUHJpbnQgaGVscCBtZXNzYWdlXG4gKi9cbmZ1bmN0aW9uIHByaW50SGVscCAoKTogdm9pZCB7XG5cdGNvbnNvbGUubG9nKGBcblRhY3RpY2EgLSBUeXBlIGRlZmluaXRpb24gZ2VuZXJhdG9yIGZvciBNbmVtb25pY2FcblxuVXNhZ2U6IHRhY3RpY2EgW29wdGlvbnNdXG5cbk9wdGlvbnM6XG4gIC13LCAtLXdhdGNoICAgICAgICAgICAgICAgV2F0Y2ggZm9yIGZpbGUgY2hhbmdlcyBhbmQgcmVnZW5lcmF0ZSB0eXBlc1xuICAtcCwgLS1wcm9qZWN0ICAgICAgICAgICAgIFBhdGggdG8gdHNjb25maWcuanNvbiAoZGVmYXVsdDogLi90c2NvbmZpZy5qc29uKVxuICAtbywgLS1vdXRwdXQgICAgICAgICAgICAgIE91dHB1dCBkaXJlY3RvcnkgZm9yIGdlbmVyYXRlZCB0eXBlcyAoZGVmYXVsdDogLnRhY3RpY2EpXG4gIC1pLCAtLWluY2x1ZGUgICAgICAgICAgICAgQ29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgZmlsZSBwYXR0ZXJucyB0byBpbmNsdWRlXG4gIC1lLCAtLWV4Y2x1ZGUgICAgICAgICAgICAgQ29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgZmlsZSBwYXR0ZXJucyB0byBleGNsdWRlXG4gIC10LCAtLXRvcG9sb2dpY2EgICAgICAgICAgQ29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgdG9wb2xvZ2ljYSBkaXJlY3RvcmllcyB0byBzY2FuXG4gIC1tLCAtLW1vZHVsZS1hdWdtZW50YXRpb24gVXNlIG1vZHVsZSBhdWdtZW50YXRpb24gaW5zdGVhZCBvZiBnbG9iYWwgKGxlZ2FjeSBtb2RlKVxuICAtLWVzbSAgICAgICAgICAgICAgICAgICAgIEFkZCAuanMgZXh0ZW5zaW9ucyB0byByZWxhdGl2ZSBpbXBvcnRzIChOb2RlTmV4dCBFU00pXG4gIC0tZWRzICAgICAgICAgICAgICAgICAgICAgRW5hYmxlIEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdHJhY2tpbmdcbiAgLS1uby1lZHMgICAgICAgICAgICAgICAgICBEaXNhYmxlIEVEUyB0cmFja2luZ1xuICAtdiwgLS12ZXJib3NlICAgICAgICAgICAgIEVuYWJsZSB2ZXJib3NlIGxvZ2dpbmdcbiAgLWgsIC0taGVscCAgICAgICAgICAgICAgICBTaG93IHRoaXMgaGVscCBtZXNzYWdlXG5cbkNvbmZpZ3VyYXRpb246XG4gIEZyYW1ld29yayBpbnN0cnVtZW50YXRpb24gdm9jYWJ1bGFyeSBpcyBzdXBwbGllZCBieSBwbHVnaW5zLiBQbGFjZSBhXG4gIC50YWN0aWNhLmpzIChvciB0YWN0aWNhLmNvbmZpZy5qcykgbmV4dCB0byB5b3VyIHRzY29uZmlnLmpzb246XG5cbiAgICAgIG1vZHVsZS5leHBvcnRzID0geyBwbHVnaW5zOiBbICd5b3VyLWZyYW1ld29yay1hZGFwdGVyL3RhY3RpY2EnIF0gfTtcblxuICBFbnRyaWVzIGFyZSBtb2R1bGUgc3BlY2lmaWVycyAocmVxdWlyZWQgcmVsYXRpdmUgdG8gdGhlIGNvbmZpZyBmaWxlKSBvclxuICBpbmxpbmUgcGx1Z2luIG9iamVjdHMuIFdpdGhvdXQgcGx1Z2lucywgaW5zdHJ1bWVudGF0aW9uLmpzb24gcG9pbnRzID0gW10uXG5cbkV4YW1wbGVzOlxuICB0YWN0aWNhICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIyBHZW5lcmF0ZSB0eXBlcyB3aXRoIGdsb2JhbCBhdWdtZW50YXRpb24gKGRlZmF1bHQpXG4gIHRhY3RpY2EgLS13YXRjaCAgICAgICAgICAgICAgICAgICAgICAjIFdhdGNoIG1vZGVcbiAgdGFjdGljYSAtLW1vZHVsZS1hdWdtZW50YXRpb24gICAgICAgICMgVXNlIGxlZ2FjeSBtb2R1bGUgYXVnbWVudGF0aW9uIG1vZGVcbiAgdGFjdGljYSAtLXByb2plY3QgLi9zcmMvdHNjb25maWcuanNvbiAjIEN1c3RvbSB0c2NvbmZpZyBwYXRoXG4gIHRhY3RpY2EgLS1vdXRwdXQgLi90eXBlcy9tbmVtb25pY2EgICAjIEN1c3RvbSBvdXRwdXQgZGlyZWN0b3J5XG4gIHRhY3RpY2EgLS10b3BvbG9naWNhIC4vc3JjL2FpLXR5cGVzICAjIFNjYW4gc3BlY2lmaWMgdG9wb2xvZ2ljYSBkaXJlY3RvcnlcbmApO1xufVxuXG4vKipcbiAqIEZpbmQgdHNjb25maWcuanNvblxuICovXG5mdW5jdGlvbiBmaW5kVHNDb25maWcgKHByb2plY3RQYXRoPzogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0aWYgKHByb2plY3RQYXRoKSB7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmMocHJvamVjdFBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gcHJvamVjdFBhdGg7XG5cdFx0fVxuXHRcdHRocm93IG5ldyBFcnJvcihgUHJvamVjdCBmaWxlIG5vdCBmb3VuZDogJHtwcm9qZWN0UGF0aH1gKTtcblx0fVxuXG5cdC8vIExvb2sgZm9yIHRzY29uZmlnLmpzb24gaW4gY3VycmVudCBkaXJlY3RvcnkgYW5kIHBhcmVudCBkaXJlY3Rvcmllc1xuXHRsZXQgY3VycmVudERpciA9IHByb2Nlc3MuY3dkKCk7XG5cdHdoaWxlIChjdXJyZW50RGlyICE9PSBwYXRoLmRpcm5hbWUoY3VycmVudERpcikpIHtcblx0XHRjb25zdCB0c2NvbmZpZ1BhdGggPSBwYXRoLmpvaW4oY3VycmVudERpciwgJ3RzY29uZmlnLmpzb24nKTtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyh0c2NvbmZpZ1BhdGgpKSB7XG5cdFx0XHRyZXR1cm4gdHNjb25maWdQYXRoO1xuXHRcdH1cblx0XHRjdXJyZW50RGlyID0gcGF0aC5kaXJuYW1lKGN1cnJlbnREaXIpO1xuXHR9XG5cblx0cmV0dXJuIHVuZGVmaW5lZDtcbn1cblxuLyoqXG4gKiBMb2FkIFR5cGVTY3JpcHQgcHJvZ3JhbSBmcm9tIHRzY29uZmlnXG4gKi9cbmZ1bmN0aW9uIGxvYWRQcm9ncmFtICh0c2NvbmZpZ1BhdGg6IHN0cmluZyk6IHRzLlByb2dyYW0ge1xuXHRjb25zdCBjb25maWdGaWxlID0gdHMucmVhZENvbmZpZ0ZpbGUodHNjb25maWdQYXRoLCB0cy5zeXMucmVhZEZpbGUpO1xuXG5cdGlmIChjb25maWdGaWxlLmVycm9yKSB7XG5cdFx0Y29uc3QgZXJyb3JUZXh0ID0gdHMuZmxhdHRlbkRpYWdub3N0aWNNZXNzYWdlVGV4dChcblx0XHRcdGNvbmZpZ0ZpbGUuZXJyb3IubWVzc2FnZVRleHQsXG5cdFx0XHQnXFxuJ1xuXHRcdCk7XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBFcnJvciByZWFkaW5nIHRzY29uZmlnOiAke2Vycm9yVGV4dH1gKTtcblx0fVxuXG5cdGNvbnN0IHBhcnNlZENvbmZpZyA9IHRzLnBhcnNlSnNvbkNvbmZpZ0ZpbGVDb250ZW50KFxuXHRcdGNvbmZpZ0ZpbGUuY29uZmlnLFxuXHRcdHRzLnN5cyxcblx0XHRwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKVxuXHQpO1xuXG5cdGlmIChwYXJzZWRDb25maWcuZXJyb3JzLmxlbmd0aCA+IDApIHtcblx0XHRjb25zdCBlcnJvck1lc3NhZ2VzID0gcGFyc2VkQ29uZmlnLmVycm9ycy5tYXAoZSA9PlxuXHRcdFx0dHMuZmxhdHRlbkRpYWdub3N0aWNNZXNzYWdlVGV4dChlLm1lc3NhZ2VUZXh0LCAnXFxuJykpO1xuXHRcdHRocm93IG5ldyBFcnJvcihgRXJyb3IgcGFyc2luZyB0c2NvbmZpZzogJHtlcnJvck1lc3NhZ2VzLmpvaW4oJ1xcbicpfWApO1xuXHR9XG5cblx0Y29uc3QgcHJvZ3JhbSA9IHRzLmNyZWF0ZVByb2dyYW0oe1xuXHRcdHJvb3ROYW1lcyA6IHBhcnNlZENvbmZpZy5maWxlTmFtZXMsXG5cdFx0b3B0aW9ucyAgIDogcGFyc2VkQ29uZmlnLm9wdGlvbnMsXG5cdH0pO1xuXG5cdHJldHVybiBwcm9ncmFtO1xufVxuXG4vKipcbiAqIExvb2sgdXAgYSB2YXJpYWJsZSBieSBuYW1lIHN0YXJ0aW5nIGZyb20gYSBzY29wZSwgd2Fsa2luZyBvdXR3YXJkIHRocm91Z2hcbiAqIHBhcmVudFNjb3BlSWQuIFRoZSBpbm5lcm1vc3QgYmluZGluZyB3aW5zIGV2ZW4gd2hlbiBpdCBjYXJyaWVzIG5vIHR5cGVQYXRoXG4gKiAoc2hhZG93aW5nIGhvbmVzdHkg4oCUIGFuIHVudHlwZWQgbG9jYWwgc2hhZG93cyBhIHR5cGVkIG91dGVyIG9uZSkuXG4gKi9cbmZ1bmN0aW9uIHJlc29sdmVTY29wZWRWYXJpYWJsZVR5cGVQYXRoIChcblx0bmFtZTogc3RyaW5nLFxuXHRzY29wZUlkOiBzdHJpbmcsXG5cdHNjb3BlQW5hbHlzaXM6IFNjb3BlQW5hbHlzaXNcbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdGxldCBjdXJyZW50OiBzdHJpbmcgfCB1bmRlZmluZWQgPSBzY29wZUlkO1xuXHR3aGlsZSAoY3VycmVudCkge1xuXHRcdGNvbnN0IHZhcmlhYmxlID0gc2NvcGVBbmFseXNpcy52YXJpYWJsZXMuZ2V0KGAke2N1cnJlbnR9IyR7bmFtZX1gKTtcblx0XHRpZiAodmFyaWFibGUpIHtcblx0XHRcdGNvbnN0IHsgdHlwZVBhdGggfSA9IHZhcmlhYmxlO1xuXHRcdFx0cmV0dXJuIHR5cGVQYXRoO1xuXHRcdH1cblx0XHRjdXJyZW50ID0gc2NvcGVBbmFseXNpcy5zY29wZXMuZ2V0KGN1cnJlbnQpPy5wYXJlbnRTY29wZUlkO1xuXHR9XG5cdHJldHVybiB1bmRlZmluZWQ7XG59XG5cbi8qKlxuICogSm9pbiBkYXRhIGZvciBtbmVtb2dyYXBoaWNhJ3Mgd3JhcHBlcnMgbGF5ZXI6IHBpbiBlYWNoIHdyYXAgZW50cnkgdG8gdGhlXG4gKiBzY29wZSBob2xkaW5nIGl0cyBjYWxsIHNpdGUsIGFuZCByZXNvbHZlIHRoZSB3cmFwcGVkIGluc3RhbmNlIGFyZ3VtZW50J3NcbiAqIG1uZW1vbmljYSB0eXBlIHRocm91Z2ggdGhlIHNjb3BlLXZhcmlhYmxlIGNoYWluLlxuICovXG5mdW5jdGlvbiBhdHRhY2hXcmFwSm9pbkRhdGEgKFxuXHRlZHM6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4sXG5cdHNjb3BlV2Fsa2VyOiBMb2NhbFNjb3BlV2Fsa2VyLFxuXHRzY29wZUFuYWx5c2lzOiBTY29wZUFuYWx5c2lzXG4pOiB2b2lkIHtcblx0Zm9yIChjb25zdCBlbnRyaWVzIG9mIGVkcy52YWx1ZXMoKSkge1xuXHRcdGZvciAoY29uc3QgZW50cnkgb2YgZW50cmllcykge1xuXHRcdFx0aWYgKGVudHJ5LmtpbmQgIT09ICd3cmFwJykge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGhvbGRlclNjb3BlSWQgPSBzY29wZVdhbGtlci5maW5kSG9sZGVyU2NvcGVJZChlbnRyeS5sb2NhdGlvbik7XG5cdFx0XHRpZiAoIWhvbGRlclNjb3BlSWQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRlbnRyeS5zY29wZUlkID0gaG9sZGVyU2NvcGVJZDtcblx0XHRcdGlmICghZW50cnkuaW5zdGFuY2VBcmcpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB3cmFwc1R5cGVQYXRoID0gcmVzb2x2ZVNjb3BlZFZhcmlhYmxlVHlwZVBhdGgoXG5cdFx0XHRcdGVudHJ5Lmluc3RhbmNlQXJnLFxuXHRcdFx0XHRob2xkZXJTY29wZUlkLFxuXHRcdFx0XHRzY29wZUFuYWx5c2lzXG5cdFx0XHQpO1xuXHRcdFx0aWYgKHdyYXBzVHlwZVBhdGgpIHtcblx0XHRcdFx0ZW50cnkud3JhcHNUeXBlUGF0aCA9IHdyYXBzVHlwZVBhdGg7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG59XG5cbi8qKlxuICogUmVuZGVyIHR5cGUgaGllcmFyY2h5IGFzIGFuIEFTQ0lJIHRyZWUgc3RyaW5nLlxuICovXG5mdW5jdGlvbiByZW5kZXJUeXBlSGllcmFyY2h5IChncmFwaDogVHlwZUdyYXBoSW1wbCk6IHN0cmluZyB7XG5cdGNvbnN0IGxpbmVzOiBzdHJpbmdbXSA9IFsgJ1R5cGUgSGllcmFyY2h5IChUcmllKTonIF07XG5cblx0ZnVuY3Rpb24gcmVuZGVyTm9kZSAobm9kZTogVHlwZU5vZGUsIHByZWZpeCA9ICcnLCBpc0xhc3QgPSB0cnVlKTogdm9pZCB7XG5cdFx0Y29uc3QgY29ubmVjdG9yID0gaXNMYXN0ID8gJ+KUlOKUgOKUgCAnIDogJ+KUnOKUgOKUgCAnO1xuXHRcdC8vIFVzZSBub2RlLmZ1bGxQYXRoIGRpcmVjdGx5IGFuZCBjb252ZXJ0IGRvdHMgdG8gdW5kZXJzY29yZXNcblx0XHRjb25zdCBpbnN0YW5jZU5hbWUgPSBub2RlLmZ1bGxQYXRoLnJlcGxhY2UoL1xcLi9nLCAnXycpO1xuXHRcdGxpbmVzLnB1c2goYCR7cHJlZml4fSR7Y29ubmVjdG9yfSR7aW5zdGFuY2VOYW1lfWApO1xuXG5cdFx0Y29uc3QgY2hpbGRyZW4gPSBBcnJheS5mcm9tKG5vZGUuY2hpbGRyZW4udmFsdWVzKCkpO1xuXHRcdGNvbnN0IG5ld1ByZWZpeCA9IHByZWZpeCArIChpc0xhc3QgPyAnICAgICcgOiAn4pSCICAgJyk7XG5cblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IGNoaWxkcmVuLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRyZW5kZXJOb2RlKGNoaWxkcmVuWyBpIF0sIG5ld1ByZWZpeCwgaSA9PT0gY2hpbGRyZW4ubGVuZ3RoIC0gMSk7XG5cdFx0fVxuXHR9XG5cblx0Y29uc3Qgcm9vdHMgPSBBcnJheS5mcm9tKGdyYXBoLnJvb3RzLnZhbHVlcygpKTtcblx0Zm9yIChsZXQgaSA9IDA7IGkgPCByb290cy5sZW5ndGg7IGkrKykge1xuXHRcdHJlbmRlck5vZGUocm9vdHNbIGkgXSwgJycsIGkgPT09IHJvb3RzLmxlbmd0aCAtIDEpO1xuXHR9XG5cdC8vIEVtcHR5IGxpbmUgYXQgZW5kXG5cdGxpbmVzLnB1c2goJycpO1xuXG5cdGNvbnN0IHJlc3VsdCA9IGxpbmVzLmpvaW4oJ1xcbicpO1xuXHRyZXR1cm4gcmVzdWx0O1xufVxuXG4vKipcbiAqIFByaW50IHR5cGUgaGllcmFyY2h5IHRvIHRoZSBjb25zb2xlLlxuICovXG5mdW5jdGlvbiBwcmludFR5cGVIaWVyYXJjaHkgKGdyYXBoOiBUeXBlR3JhcGhJbXBsKTogdm9pZCB7XG5cdGNvbnN0IG91dHB1dCA9IHJlbmRlclR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHRjb25zb2xlLmxvZyhvdXRwdXQpO1xufVxuXG4vKipcbiAqIENoZWNrIGlmIEBtbmVtb25pY2EvZGl2ZSBpcyBwcmVzZW50IGluIHBhY2thZ2UuanNvbiBkZXBlbmRlbmNpZXNcbiAqL1xuZnVuY3Rpb24gaGFzRGl2ZURlcGVuZGVuY3kgKHByb2plY3REaXI6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRjb25zdCBwYWNrYWdlSnNvblBhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgJ3BhY2thZ2UuanNvbicpO1xuXHRpZiAoIWZzLmV4aXN0c1N5bmMocGFja2FnZUpzb25QYXRoKSkge1xuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXHR0cnkge1xuXHRcdGNvbnN0IGNvbnRlbnQgPSBmcy5yZWFkRmlsZVN5bmMocGFja2FnZUpzb25QYXRoLCAndXRmLTgnKTtcblx0XHRjb25zdCBwa2cgPSBKU09OLnBhcnNlKGNvbnRlbnQpO1xuXHRcdGNvbnN0IGRlcHMgPSBwa2cuZGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdGNvbnN0IGRldkRlcHMgPSBwa2cuZGV2RGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdGNvbnN0IHBlZXJEZXBzID0gcGtnLnBlZXJEZXBlbmRlbmNpZXMgfHwge307XG5cdFx0cmV0dXJuICdAbW5lbW9uaWNhL2RpdmUnIGluIGRlcHMgfHwgJ0BtbmVtb25pY2EvZGl2ZScgaW4gZGV2RGVwcyB8fCAnQG1uZW1vbmljYS9kaXZlJyBpbiBwZWVyRGVwcztcblx0fSBjYXRjaCB7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG59XG5cbi8qKlxuICogU2NhbiBmb3IgdG9wb2xvZ2ljYSBkaXJlY3Rvcnkgc3RydWN0dXJlc1xuICovXG5mdW5jdGlvbiBzY2FuVG9wb2xvZ2ljYURpcmVjdG9yaWVzIChwcm9qZWN0RGlyOiBzdHJpbmcsIGN1c3RvbURpcnM/OiBzdHJpbmdbXSk6IHN0cmluZ1tdIHtcblx0Y29uc3QgZGlyczogc3RyaW5nW10gPSBbXTtcblxuXHQvLyBGaXJzdCwgYWRkIGN1c3RvbSBkaXJlY3RvcmllcyBpZiBzcGVjaWZpZWRcblx0aWYgKGN1c3RvbURpcnMpIHtcblx0XHRmb3IgKGNvbnN0IGRpciBvZiBjdXN0b21EaXJzKSB7XG5cdFx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5pc0Fic29sdXRlKGRpcikgPyBkaXIgOiBwYXRoLmpvaW4ocHJvamVjdERpciwgZGlyKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc29sZS53YXJuKGBXYXJuaW5nOiBUb3BvbG9naWNhIGRpcmVjdG9yeSBub3QgZm91bmQ6ICR7ZGlyUGF0aH1gKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvLyBUaGVuIGF1dG8tZGlzY292ZXIgc3RhbmRhcmQgdG9wb2xvZ2ljYSBkaXJlY3Rvcmllc1xuXHRjb25zdCBwb3NzaWJsZURpcnMgPSBbICdhaS10eXBlcycsICd0eXBlcycsICd0b3BvbG9naWNhLXR5cGVzJyBdO1xuXG5cdGZvciAoY29uc3QgZGlyTmFtZSBvZiBwb3NzaWJsZURpcnMpIHtcblx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsIGRpck5hbWUpO1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdC8vIEF2b2lkIGR1cGxpY2F0ZXNcblx0XHRcdGlmICghZGlycy5pbmNsdWRlcyhkaXJQYXRoKSkge1xuXHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWxzbyBzY2FuIHNyYy8gc3ViZGlyZWN0b3J5XG5cdGNvbnN0IHNyY1BhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgJ3NyYycpO1xuXHRpZiAoZnMuZXhpc3RzU3luYyhzcmNQYXRoKSAmJiBmcy5zdGF0U3luYyhzcmNQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0Zm9yIChjb25zdCBkaXJOYW1lIG9mIHBvc3NpYmxlRGlycykge1xuXHRcdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguam9pbihzcmNQYXRoLCBkaXJOYW1lKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdFx0Ly8gQXZvaWQgZHVwbGljYXRlc1xuXHRcdFx0XHRpZiAoIWRpcnMuaW5jbHVkZXMoZGlyUGF0aCkpIHtcblx0XHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gZGlycztcbn1cblxuLyoqXG4gKiBDb25maWcgZmlsZSBjYW5kaWRhdGVzIChlc2xpbnQtc3R5bGUgcHJvamVjdCBjb25maWcpLCBzZWFyY2hlZCBuZXh0IHRvXG4gKiB0aGUgcmVzb2x2ZWQgdHNjb25maWcgZmlyc3QsIHRoZW4gaW4gdGhlIGN1cnJlbnQgd29ya2luZyBkaXJlY3RvcnkuXG4gKi9cbmNvbnN0IENPTkZJR19GSUxFX05BTUVTID0gWyAnLnRhY3RpY2EuanMnLCAndGFjdGljYS5jb25maWcuanMnIF07XG5cbmludGVyZmFjZSBUYWN0aWNhQ29uZmlnRmlsZSB7XG5cdHBsdWdpbnM/OiBBcnJheTxUYWN0aWNhUGx1Z2luIHwgc3RyaW5nPjtcbn1cblxuLyoqXG4gKiBMb2FkIGZyYW1ld29yay12b2NhYnVsYXJ5IHBsdWdpbnM6IHByb2dyYW1tYXRpYyBvcHRpb25zIGZpcnN0LCB0aGVuIHRoZVxuICogcHJvamVjdCBjb25maWcgZmlsZS4gU3RyaW5nIGVudHJpZXMgYXJlIG1vZHVsZSBzcGVjaWZpZXJzIHJlcXVpcmVkXG4gKiByZWxhdGl2ZSB0byB0aGUgY29uZmlnIGZpbGUgKGUuZy4gYW4gYWRhcHRlciBwYWNrYWdlJ3MgcGx1Z2luIHN1YnBhdGgpLlxuICogV2l0aG91dCBhIGNvbmZpZyBmaWxlIGFuZCB3aXRob3V0IHByb2dyYW1tYXRpYyBwbHVnaW5zIHRoZSBhbmFseXplclxuICogc3RheXMgZnJhbWV3b3JrLWJsaW5kIGFuZCBpbnN0cnVtZW50YXRpb24uanNvbiBjYXJyaWVzIGVtcHR5IHBvaW50cy5cbiAqL1xuZnVuY3Rpb24gbG9hZFRhY3RpY2FQbHVnaW5zIChwcm9qZWN0RGlyOiBzdHJpbmcsIG9wdGlvbnM6IENMSU9wdGlvbnMpOiBUYWN0aWNhUGx1Z2luW10ge1xuXHRjb25zdCBwbHVnaW5zOiBUYWN0aWNhUGx1Z2luW10gPSBbIC4uLihvcHRpb25zLnBsdWdpbnMgfHwgW10pIF07XG5cblx0Y29uc3Qgc2VhcmNoRGlycyA9IFsgcHJvamVjdERpciBdO1xuXHRjb25zdCBjd2QgPSBwcm9jZXNzLmN3ZCgpO1xuXHRpZiAoY3dkICE9PSBwcm9qZWN0RGlyKSB7XG5cdFx0c2VhcmNoRGlycy5wdXNoKGN3ZCk7XG5cdH1cblxuXHRsZXQgY29uZmlnUGF0aDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRmb3IgKGNvbnN0IGRpciBvZiBzZWFyY2hEaXJzKSB7XG5cdFx0Zm9yIChjb25zdCBuYW1lIG9mIENPTkZJR19GSUxFX05BTUVTKSB7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGUgPSBwYXRoLmpvaW4oZGlyLCBuYW1lKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGNhbmRpZGF0ZSkpIHtcblx0XHRcdFx0Y29uZmlnUGF0aCA9IGNhbmRpZGF0ZTtcblx0XHRcdFx0YnJlYWs7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChjb25maWdQYXRoKSB7XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdH1cblxuXHRpZiAoIWNvbmZpZ1BhdGgpIHtcblx0XHRyZXR1cm4gcGx1Z2lucztcblx0fVxuXG5cdC8vIGNyZWF0ZVJlcXVpcmUgYW5jaG9yZWQgYXQgdGhlIGNvbmZpZyBmaWxlOiB0aGUgY29uZmlnJ3Mgb3duIGltcG9ydHNcblx0Ly8gYW5kIHN0cmluZyBwbHVnaW4gc3BlY2lmaWVycyByZXNvbHZlIGFnYWluc3QgdGhlIHByb2plY3QncyBtb2R1bGVzXG5cdGNvbnN0IGNvbmZpZ1JlcXVpcmUgPSBjcmVhdGVSZXF1aXJlKGNvbmZpZ1BhdGgpO1xuXHRjb25zdCBsb2FkZWQgPSBjb25maWdSZXF1aXJlKGNvbmZpZ1BhdGgpO1xuXHRjb25zdCBjb25maWc6IFRhY3RpY2FDb25maWdGaWxlID0gbG9hZGVkICYmIHR5cGVvZiBsb2FkZWQgPT09ICdvYmplY3QnICYmICdkZWZhdWx0JyBpbiBsb2FkZWRcblx0XHQ/IGxvYWRlZC5kZWZhdWx0XG5cdFx0OiBsb2FkZWQ7XG5cdGNvbnN0IGVudHJpZXMgPSBjb25maWcgJiYgQXJyYXkuaXNBcnJheShjb25maWcucGx1Z2lucykgPyBjb25maWcucGx1Z2lucyA6IFtdO1xuXG5cdGZvciAoY29uc3QgZW50cnkgb2YgZW50cmllcykge1xuXHRcdGlmICh0eXBlb2YgZW50cnkgIT09ICdzdHJpbmcnKSB7XG5cdFx0XHRwbHVnaW5zLnB1c2goZW50cnkpO1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXHRcdGNvbnN0IG1vZCA9IGNvbmZpZ1JlcXVpcmUoZW50cnkpO1xuXHRcdGNvbnN0IHBsdWdpbjogVGFjdGljYVBsdWdpbiA9IG1vZCAmJiB0eXBlb2YgbW9kID09PSAnb2JqZWN0JyAmJiAnZGVmYXVsdCcgaW4gbW9kXG5cdFx0XHQ/IG1vZC5kZWZhdWx0XG5cdFx0XHQ6IG1vZDtcblx0XHRwbHVnaW5zLnB1c2gocGx1Z2luKTtcblx0fVxuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBuYW1lcyA9IHBsdWdpbnMubWFwKHBsdWdpbiA9PiBwbHVnaW4ubmFtZSB8fCAnKHVubmFtZWQpJykuam9pbignLCAnKTtcblx0XHRjb25zb2xlLmxvZyhgTG9hZGVkIHRhY3RpY2EgY29uZmlnOiAke2NvbmZpZ1BhdGh9IChwbHVnaW5zOiAke25hbWVzIHx8ICdub25lJ30pYCk7XG5cdH1cblxuXHRyZXR1cm4gcGx1Z2lucztcbn1cblxuLyoqXG4gKiBSdW4gdHlwZSBnZW5lcmF0aW9uLiBSZXR1cm5zIDAgb24gc3VjY2VzczsgMSB3aGVuIHRoZSBncmFwaCBpZGVudGl0eSBsYXdcbiAqIGFib3J0ZWQgdGhlIHJ1biAoZmFpbHVyZXMgcHJpbnRlZCwgbm8gLnRhY3RpY2Egb3V0cHV0IHdyaXR0ZW4pLlxuICovXG5mdW5jdGlvbiBydW4gKG9wdGlvbnM6IENMSU9wdGlvbnMpOiBudW1iZXIge1xuXHRjb25zdCB0c2NvbmZpZ1BhdGggPSBmaW5kVHNDb25maWcob3B0aW9ucy5wcm9qZWN0KTtcblxuXHRpZiAoIXRzY29uZmlnUGF0aCkge1xuXHRcdGNvbnNvbGUuZXJyb3IoJ0Vycm9yOiBDb3VsZCBub3QgZmluZCB0c2NvbmZpZy5qc29uJyk7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBVc2luZyB0c2NvbmZpZzogJHt0c2NvbmZpZ1BhdGh9YCk7XG5cdH1cblxuXHQvLyBGcmFtZXdvcmsgdm9jYWJ1bGFyeSBhcnJpdmVzIHZpYSBwbHVnaW5zIOKAlCBhIGNvbmZpZyBmaWxlIG5leHQgdG8gdGhlXG5cdC8vIHRzY29uZmlnIChvciBpbiBjd2QpIGFuZC9vciBwcm9ncmFtbWF0aWMgb3B0aW9ucy4gTm9uZSBsb2FkZWQgbWVhbnNcblx0Ly8gdGhlIGFuYWx5emVyIGRldGVjdHMgemVybyBpbnN0cnVtZW50YXRpb24gcG9pbnRzLlxuXHRjb25zdCBwbHVnaW5zID0gbG9hZFRhY3RpY2FQbHVnaW5zKHBhdGguZGlybmFtZShwYXRoLnJlc29sdmUodHNjb25maWdQYXRoKSksIG9wdGlvbnMpO1xuXG5cdC8vIExvYWQgVHlwZVNjcmlwdCBwcm9ncmFtXG5cdGNvbnN0IHByb2dyYW0gPSBsb2FkUHJvZ3JhbSh0c2NvbmZpZ1BhdGgpO1xuXG5cdC8vIENyZWF0ZSBhbmFseXplclxuXHRjb25zdCBhbmFseXplciA9IG5ldyBNbmVtb25pY2FBbmFseXplcihwcm9ncmFtLCBwbHVnaW5zKTtcblxuXHQvLyBEZXRlcm1pbmUgb3V0cHV0IGRpcmVjdG9yeSBmb3IgZXhjbHVzaW9uXG5cdGNvbnN0IG91dHB1dERpciA9IG9wdGlvbnMub3V0cHV0RGlyIHx8ICcudGFjdGljYSc7XG5cdGNvbnN0IG91dHB1dERpclBhdGggPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgb3V0cHV0RGlyKTtcblx0Ly8gVGhlIHByb2plY3QtY29udmVudGlvbmFsIC50YWN0aWNhIGRpciAobmV4dCB0byB0c2NvbmZpZykgaXMgQUxXQVlTXG5cdC8vIGV4Y2x1ZGVkLCBldmVuIHdoZW4gLS1vdXRwdXQgcG9pbnRzIGVsc2V3aGVyZTogZ2VuZXJhdGVkIGZpbGVzIGFyZVxuXHQvLyBuZXZlciBwcm9qZWN0IHNvdXJjZS4gcmVzb2x2ZSgpIGJvdGggc2lkZXMg4oCUIHRzY29uZmlnUGF0aCBtYXkgYmVcblx0Ly8gcmVsYXRpdmUgKCcuL3RzY29uZmlnLmpzb24nKSB3aGlsZSBzb3VyY2VGaWxlLmZpbGVOYW1lIGlzIGFic29sdXRlXG5cdGNvbnN0IGNvbnZlbnRpb25hbE91dHB1dERpciA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKSwgJy50YWN0aWNhJyk7XG5cblx0Ly8gQ29sbGVjdCBzb3VyY2UgZmlsZXMgdG8gYW5hbHl6ZVxuXHRjb25zdCBzb3VyY2VGaWxlczogdHMuU291cmNlRmlsZVtdID0gW107XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBwcm9ncmFtLmdldFNvdXJjZUZpbGVzKCkpIHtcblx0XHRpZiAoc291cmNlRmlsZS5pc0RlY2xhcmF0aW9uRmlsZSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QgYWJzb2x1dGVGaWxlTmFtZSA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBzb3VyY2VGaWxlLmZpbGVOYW1lKTtcblx0XHRpZiAoYWJzb2x1dGVGaWxlTmFtZS5zdGFydHNXaXRoKG91dHB1dERpclBhdGggKyBwYXRoLnNlcCkgfHxcblx0XHRcdGFic29sdXRlRmlsZU5hbWUuc3RhcnRzV2l0aChjb252ZW50aW9uYWxPdXRwdXREaXIgKyBwYXRoLnNlcCkpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGV4Y2x1ZGUgcGF0dGVybnNcblx0XHRpZiAob3B0aW9ucy5leGNsdWRlKSB7XG5cdFx0XHRjb25zdCBzaG91bGRFeGNsdWRlID0gb3B0aW9ucy5leGNsdWRlLnNvbWUocGF0dGVybiA9PlxuXHRcdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLmluY2x1ZGVzKHBhdHRlcm4ucmVwbGFjZSgvXFwqL2csICcnKSkpO1xuXHRcdFx0aWYgKHNob3VsZEV4Y2x1ZGUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgaW5jbHVkZSBwYXR0ZXJuc1xuXHRcdGlmIChvcHRpb25zLmluY2x1ZGUgJiYgb3B0aW9ucy5pbmNsdWRlLmxlbmd0aCA+IDApIHtcblx0XHRcdGNvbnN0IHNob3VsZEluY2x1ZGUgPSBvcHRpb25zLmluY2x1ZGUuc29tZShwYXR0ZXJuID0+XG5cdFx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUuaW5jbHVkZXMocGF0dGVybi5yZXBsYWNlKC9cXCovZywgJycpKSk7XG5cdFx0XHRpZiAoIXNob3VsZEluY2x1ZGUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0c291cmNlRmlsZXMucHVzaChzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8vIFNjYW4gZm9yIHRvcG9sb2dpY2EgZGlyZWN0b3J5IHN0cnVjdHVyZXMgRklSU1Rcblx0Y29uc3QgcHJvamVjdERpciA9IHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpO1xuXHRjb25zdCB0b3BvbG9naWNhRGlycyA9IHNjYW5Ub3BvbG9naWNhRGlyZWN0b3JpZXMocHJvamVjdERpciwgb3B0aW9ucy50b3BvbG9naWNhRGlycyk7XG5cblx0aWYgKHRvcG9sb2dpY2FEaXJzLmxlbmd0aCA+IDAgJiYgb3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEZvdW5kIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXM6ICR7dG9wb2xvZ2ljYURpcnMuam9pbignLCAnKX1gKTtcblx0fVxuXG5cdC8vIEFuYWx5emUgdG9wb2xvZ2ljYSBkaXJlY3RvcmllcyBCRUZPUkUgdXNhZ2UgY29sbGVjdGlvblxuXHRjb25zdCB0b3BvbG9naWNhQW5hbHl6ZXIgPSBuZXcgVG9wb2xvZ2ljYUFuYWx5emVyKCk7XG5cdGNvbnN0IHRvcG9sb2dpY2FUeXBlcyA9IG5ldyBNYXA8c3RyaW5nLCBpbXBvcnQoJy4vdHlwZXMnKS5UeXBlTm9kZT4oKTtcblx0Zm9yIChjb25zdCBkaXIgb2YgdG9wb2xvZ2ljYURpcnMpIHtcblx0XHRjb25zdCByZXN1bHQgPSB0b3BvbG9naWNhQW5hbHl6ZXIuYW5hbHl6ZURpcmVjdG9yeShkaXIpO1xuXHRcdGlmIChyZXN1bHQudHlwZXMuc2l6ZSA+IDApIHtcblx0XHRcdC8vIENvbGxlY3QgdG9wb2xvZ2ljYSB0eXBlcyBmb3IgZGVmaW5pdGlvbnMgYW5kIHVzYWdlIHRyYWNraW5nXG5cdFx0XHRmb3IgKGNvbnN0IFsgdHlwZVBhdGgsIG5vZGUgXSBvZiByZXN1bHQudHlwZXMpIHtcblx0XHRcdFx0dG9wb2xvZ2ljYVR5cGVzLnNldCh0eXBlUGF0aCwgbm9kZSk7XG5cdFx0XHR9XG5cdFx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRcdGNvbnNvbGUubG9nKGBBZGRlZCAke3Jlc3VsdC50eXBlcy5zaXplfSB0eXBlcyBmcm9tICR7ZGlyfWApO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAocmVzdWx0LmVycm9ycy5sZW5ndGggPiAwICYmIG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0cmVzdWx0LmVycm9ycy5mb3JFYWNoKGVyciA9PiBjb25zb2xlLndhcm4oYFtUb3BvbG9naWNhXSAke2Vycn1gKSk7XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWRkIHRvcG9sb2dpY2EgdHlwZXMgdG8gYW5hbHl6ZXIgc28gdGhleSdyZSBhdmFpbGFibGUgZm9yIHVzYWdlIGRldGVjdGlvblxuXHQvLyBQcm9jZXNzIGluIG9yZGVyIG9mIHBhdGggZGVwdGggKHBhcmVudHMgZmlyc3QpIHRvIGVuc3VyZSBwcm9wZXIgaGllcmFyY2h5XG5cdGNvbnN0IHNvcnRlZFR5cGVzID0gQXJyYXkuZnJvbSh0b3BvbG9naWNhVHlwZXMuZW50cmllcygpKS5zb3J0KChhLCBiKSA9PiB7XG5cdFx0Y29uc3QgZGVwdGhBID0gKGFbIDAgXS5tYXRjaCgvXFwuL2cpIHx8IFtdKS5sZW5ndGg7XG5cdFx0Y29uc3QgZGVwdGhCID0gKGJbIDAgXS5tYXRjaCgvXFwuL2cpIHx8IFtdKS5sZW5ndGg7XG5cdFx0cmV0dXJuIGRlcHRoQSAtIGRlcHRoQjtcblx0fSk7XG5cdGZvciAoY29uc3QgWyB0eXBlUGF0aCwgbm9kZSBdIG9mIHNvcnRlZFR5cGVzKSB7XG5cdFx0YW5hbHl6ZXIuYWRkVG9wb2xvZ2ljYVR5cGUodHlwZVBhdGgsIG5vZGUpO1xuXHR9XG5cblx0Ly8gRmlyc3QgcGFzczogY29sbGVjdCBhbGwgZGVmaW5pdGlvbnMuXG5cdC8vIE1vZHVsZS1zY29wZSB0cmFja2luZyAoaW1wb3J0cy9leHBvcnRzIGZvciBtb2R1bGVzLmpzb24pIGhhcHBlbnMgaW4gdGhlXG5cdC8vIHNhbWUgcGFzcyDigJQgaXQgbmVlZHMgb25seSB0aGUgQVNULCBub3QgdGhlIGNvbGxlY3RlZCBkZWZpbml0aW9ucy5cblx0Y29uc3QgbW9kdWxlR3JhcGhCdWlsZGVyID0gbmV3IE1vZHVsZUdyYXBoQnVpbGRlcihwcm9ncmFtKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEFuYWx5emluZyAoZGVmaW5pdGlvbnMpOiAke3NvdXJjZUZpbGUuZmlsZU5hbWV9YCk7XG5cdFx0fVxuXG5cdFx0dHJ5IHtcblx0XHRcdGFuYWx5emVyLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdFx0bW9kdWxlR3JhcGhCdWlsZGVyLmFkZEZpbGUoc291cmNlRmlsZSk7XG5cdFx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0XHRjb25zb2xlLmVycm9yKGBFcnJvciBhbmFseXppbmcgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfTpgLCBlcnIpO1xuXHRcdFx0dGhyb3cgZXJyO1xuXHRcdH1cblx0fVxuXG5cdC8vIFNlY29uZCBwYXNzOiBjb2xsZWN0IHVzYWdlcyAobm93IGFsbCBkZWZpbml0aW9ucyBhcmUga25vd24sIGluY2x1ZGluZyB0b3BvbG9naWNhKVxuXHRhbmFseXplci5yZXNldFVzYWdlcygpO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgQW5hbHl6aW5nICh1c2FnZXMpOiAke3NvdXJjZUZpbGUuZmlsZU5hbWV9YCk7XG5cdFx0fVxuXG5cdFx0dHJ5IHtcblx0XHRcdGFuYWx5emVyLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdH0gY2F0Y2ggKGVycikge1xuXHRcdFx0Y29uc29sZS5lcnJvcihgRXJyb3IgYW5hbHl6aW5nICR7c291cmNlRmlsZS5maWxlTmFtZX06YCwgZXJyKTtcblx0XHRcdHRocm93IGVycjtcblx0XHR9XG5cdH1cblxuXHQvLyBHZW5lcmF0ZSB0eXBlcyBmcm9tIG1uZW1vbmljYSBhbmFseXNpc1xuXHQvLyBOb3RlOiB0b3BvbG9naWNhIHR5cGVzIGFyZSBhbHJlYWR5IGFkZGVkIHRvIHRoZSBhbmFseXplcidzIGdyYXBoIHZpYSBhZGRUb3BvbG9naWNhVHlwZSgpXG5cdGNvbnN0IGdyYXBoID0gYW5hbHl6ZXIuZ2V0R3JhcGgoKTtcblxuXHQvLyBQYXRoLWF3YXJlIGdyYXBoIHJlZmVyZW5jZSByZXNvbHV0aW9uIChpZGVudGl0eSBsYXcpOiB0aGUgZ2VuZXJhdG9yXG5cdC8vIHJlc29sdmVzIG5hbWVzIHRocm91Z2ggdGhlIHNhbWUgcmVsYXRpdmUtZmlyc3Qvcm9vdC91bmlxdWUgdGllcnMgdGhlXG5cdC8vIGFuYWx5emVyIHVzZXM7IHRoZSBhbmFseXplcidzIG93biB2YWx1ZS9pbXBvcnQgdGllcnMgYWxyZWFkeSB2ZXR0ZWQgdGhlXG5cdC8vIHR5cGUgc3RyaW5ncyBkdXJpbmcgZXh0cmFjdGlvblxuXHRjb25zdCByZWZlcmVuY2VSZXNvbHZlcjogR3JhcGhSZWZlcmVuY2VSZXNvbHZlciA9IChzaW1wbGVOYW1lLCBhbmNob3IpID0+IHtcblx0XHRjb25zdCByZWZSZXN1bHQgPSByZXNvbHZlR3JhcGhUeXBlUmVmZXJlbmNlKGdyYXBoLCBzaW1wbGVOYW1lLCBhbmNob3IpO1xuXHRcdGlmIChyZWZSZXN1bHQuc3RhdHVzID09PSAndW5pcXVlJykge1xuXHRcdFx0cmV0dXJuIHJlZlJlc3VsdC5ub2RlO1xuXHRcdH1cblx0XHRpZiAocmVmUmVzdWx0LnN0YXR1cyA9PT0gJ2FtYmlndW91cycpIHtcblx0XHRcdHJldHVybiAnYW1iaWd1b3VzJztcblx0XHR9XG5cdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0fTtcblx0Y29uc3QgZ2VuZXJhdG9yID0gbmV3IFR5cGVzR2VuZXJhdG9yKGdyYXBoLCBvcHRpb25zLmVzbSwgb3B0aW9ucy5vdXRwdXREaXIsIHJlZmVyZW5jZVJlc29sdmVyKTtcblxuXHQvLyBDaGVjayBpZiBtb2R1bGUgYXVnbWVudGF0aW9uIG1vZGUgaXMgcmVxdWVzdGVkIChsZWdhY3kpXG5cdGNvbnN0IHVzZU1vZHVsZUF1Z21lbnRhdGlvbiA9IG9wdGlvbnMuZ2xvYmFsQXVnbWVudGF0aW9uID09PSBmYWxzZTtcblxuXHQvLyBHZW5lcmF0ZSBldmVyeXRoaW5nIGludG8gbWVtb3J5IEZJUlNUIOKAlCB0aGUgaGFyZC1mYWlsIGxhdyBiZWxvdyBtYXlcblx0Ly8gYWJvcnQgdGhlIHJ1biwgYW5kIG5vIC50YWN0aWNhIG91dHB1dCBhdCBhbGwgbWF5IGJlIHdyaXR0ZW4gdGhlblxuXHRsZXQgZ2VuZXJhdGVkVHlwZXM6IHsgY29udGVudDogc3RyaW5nOyB0eXBlczogc3RyaW5nW10gfTtcblx0bGV0IHJlZ2lzdHJ5VHlwZXM6IHsgY29udGVudDogc3RyaW5nOyB0eXBlczogc3RyaW5nW10gfSB8IHVuZGVmaW5lZDtcblx0bGV0IG91dHB1dFBhdGg6IHN0cmluZztcblxuXHRpZiAodXNlTW9kdWxlQXVnbWVudGF0aW9uKSB7XG5cdFx0Ly8gTGVnYWN5IG1vZGU6IGdlbmVyYXRlIGdsb2JhbCBhdWdtZW50YXRpb24gZmlsZSAoaW5kZXguZC50cylcblx0XHRnZW5lcmF0ZWRUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZUdsb2JhbEF1Z21lbnRhdGlvbigpO1xuXHR9IGVsc2Uge1xuXHRcdC8vIERlZmF1bHQgbW9kZTogZ2VuZXJhdGUgdHlwZXMudHMgZm9yIG1hbnVhbCBpbXBvcnRzXG5cdFx0Z2VuZXJhdGVkVHlwZXMgPSBnZW5lcmF0b3IuZ2VuZXJhdGVUeXBlc0ZpbGUoKTtcblxuXHRcdC8vIEdlbmVyYXRlIHJlZ2lzdHJ5LnRzIGZvciB0eXBlLXNhZmUgbG9va3VwKCkgZnVuY3Rpb25cblx0XHRyZWdpc3RyeVR5cGVzID0gZ2VuZXJhdG9yLmdlbmVyYXRlVHlwZVJlZ2lzdHJ5KCk7XG5cdH1cblxuXHQvLyBIQVJEIEZBSUwgKGdyYXBoIGlkZW50aXR5IGxhdyk6IHNhbWUtbmFtZXNwYWNlIGR1cGxpY2F0ZSBtbmVtb25pY2Fcblx0Ly8gZGVmaW5pdGlvbnMsIHBsdXMgZ3JhcGggcmVmZXJlbmNlcyB0aGF0IHN0YXkgYW1iaWd1b3VzIGFmdGVyXG5cdC8vIHBhdGgtYXdhcmUgcmVzb2x1dGlvbiBvciByZXNvbHZlIHRvIG5vdGhpbmcuIFByaW50IGV2ZXJ5IGZhaWx1cmUgd2l0aFxuXHQvLyBhbGwgaXRzIGxvY2F0aW9ucyBhbmQgd3JpdGUgTk8gLnRhY3RpY2Egb3V0cHV0IGF0IGFsbC5cblx0Y29uc3QgZmF0YWxFcnJvcnMgPSBbIC4uLmFuYWx5emVyLmdldFJlc29sdXRpb25FcnJvcnMoKSwgLi4uZ2VuZXJhdG9yLmdldFJlc29sdXRpb25FcnJvcnMoKSBdO1xuXHRpZiAoZmF0YWxFcnJvcnMubGVuZ3RoID4gMCkge1xuXHRcdGNvbnN0IHNlZW4gPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRsZXQgcHJpbnRlZCA9IDA7XG5cdFx0Zm9yIChjb25zdCBlcnJvciBvZiBmYXRhbEVycm9ycykge1xuXHRcdFx0Y29uc3Qga2V5ID0gYCR7ZXJyb3IubWVzc2FnZX18JHtlcnJvci5sb2NhdGlvbnMuam9pbignfCcpfWA7XG5cdFx0XHRpZiAoc2Vlbi5oYXMoa2V5KSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdHNlZW4uYWRkKGtleSk7XG5cdFx0XHRwcmludGVkKys7XG5cdFx0XHRjb25zb2xlLmVycm9yKGB0YWN0aWNhOiAke2Vycm9yLm1lc3NhZ2V9YCk7XG5cdFx0XHRmb3IgKGNvbnN0IGxvY2F0aW9uIG9mIGVycm9yLmxvY2F0aW9ucykge1xuXHRcdFx0XHRjb25zb2xlLmVycm9yKGAgIGF0ICR7bG9jYXRpb259YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnNvbGUuZXJyb3IoYHRhY3RpY2E6IGFib3J0aW5nIOKAlCAke3ByaW50ZWR9IHJlc29sdXRpb24gZmFpbHVyZShzKTsgbm8gLnRhY3RpY2Egb3V0cHV0IHdyaXR0ZW5gKTtcblx0XHRyZXR1cm4gMTtcblx0fVxuXG5cdC8vIFByb2plY3Qgcm9vdCBhbmNob3JzIHRoZSByZWxhdGl2ZSBwYXRocyB0aGUgd3JpdGVyIGVtaXRzOiAudGFjdGljYVxuXHQvLyBvdXRwdXQgbXVzdCBzdGF5IHBvcnRhYmxlIHdoZW4gdGhlIGNoZWNrb3V0IG1vdmVzIGJldHdlZW4gbWFjaGluZXMuXG5cdC8vIHJlc29sdmUoKSBib3RoIHNpZGVzIOKAlCB0c2NvbmZpZ1BhdGggaXRzZWxmIG1heSBiZSByZWxhdGl2ZS5cblx0Y29uc3QgcHJvamVjdFJvb3QgPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCkpO1xuXHRjb25zdCB3cml0ZXIgPSBuZXcgVHlwZXNXcml0ZXIob3B0aW9ucy5vdXRwdXREaXIsIHByb2plY3RSb290KTtcblxuXHRpZiAodXNlTW9kdWxlQXVnbWVudGF0aW9uKSB7XG5cdFx0Ly8gTGVnYWN5IG1vZGU6IHdyaXRlIGdsb2JhbCBhdWdtZW50YXRpb24gZmlsZSAoaW5kZXguZC50cylcblx0XHRvdXRwdXRQYXRoID0gd3JpdGVyLndyaXRlR2xvYmFsQXVnbWVudGF0aW9uKGdlbmVyYXRlZFR5cGVzKTtcblx0fSBlbHNlIHtcblx0XHQvLyBEZWZhdWx0IG1vZGU6IHdyaXRlIHR5cGVzLnRzIGZvciBtYW51YWwgaW1wb3J0c1xuXHRcdG91dHB1dFBhdGggPSB3cml0ZXIud3JpdGVUeXBlc0ZpbGUoZ2VuZXJhdGVkVHlwZXMpO1xuXG5cdFx0Y29uc3QgcmVnaXN0cnlQYXRoID0gd3JpdGVyLndyaXRlVG8oJ3JlZ2lzdHJ5LnRzJywgcmVnaXN0cnlUeXBlcyEuY29udGVudCk7XG5cblx0XHQvLyBHZW5lcmF0ZSBpbmRleC50cyB0byBleHBvcnQgZXZlcnl0aGluZ1xuXHRcdGNvbnN0IGluZGV4Q29udGVudCA9IGAvLyBHZW5lcmF0ZWQgYnkgQG1uZW1vbmljYS90YWN0aWNhIC0gRE8gTk9UIEVESVRcbi8vIEV4cG9ydCBhbGwgZ2VuZXJhdGVkIHR5cGVzXG5cbmV4cG9ydCAqIGZyb20gJy4vdHlwZXMke29wdGlvbnMuZXNtID8gJy5qcycgOiAnJ30nO1xuZXhwb3J0ICogZnJvbSAnLi9yZWdpc3RyeSR7b3B0aW9ucy5lc20gPyAnLmpzJyA6ICcnfSc7XG5gO1xuXHRcdHdyaXRlci53cml0ZVRvKCdpbmRleC50cycsIGluZGV4Q29udGVudCk7XG5cblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHJlZ2lzdHJ5LnRzIGF0OiAke3JlZ2lzdHJ5UGF0aH1gKTtcblx0XHR9XG5cdH1cblxuXHQvLyBHZW5lcmF0ZSBkZWZpbml0aW9ucy5qc29uIGFuZCB1c2FnZXMuanNvbiBmb3IgY29kZSBuYXZpZ2F0aW9uXG5cdC8vIEluY2x1ZGUgYm90aCBtbmVtb25pY2EgYW5kIHRvcG9sb2dpY2EgZGVmaW5pdGlvbnNcblx0Y29uc3QgZGVmaW5pdGlvbnMgPSBuZXcgTWFwKGFuYWx5emVyLmdldERlZmluaXRpb25zKCkpO1xuXHRjb25zdCB1c2FnZXMgPSBuZXcgTWFwKGFuYWx5emVyLmdldFVzYWdlcygpKTtcblx0XG5cdC8vIEFkZCB0b3BvbG9naWNhIHR5cGVzIHRvIGRlZmluaXRpb25zXG5cdGZvciAoY29uc3QgWyBmdWxsUGF0aCwgdHlwZU5vZGUgXSBvZiB0b3BvbG9naWNhVHlwZXMpIHtcblx0XHQvLyBTa2lwIGlmIGFscmVhZHkgZXhpc3RzIChwcmVmZXIgbW5lbW9uaWNhJ3MgYW5hbHlzaXMpXG5cdFx0aWYgKGRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblx0XHRcblx0XHRjb25zdCBkZWZpbml0aW9uOiBpbXBvcnQoJy4vdHlwZXMnKS5EZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5vZGUubmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7dHlwZU5vZGUuc291cmNlRmlsZX06JHt0eXBlTm9kZS5saW5lfToke3R5cGVOb2RlLmNvbHVtbn1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogdHlwZU5vZGUucGFyZW50ID8gdHlwZU5vZGUucGFyZW50LmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogZmFsc2Vcblx0XHR9O1xuXHRcdGRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdH1cblxuXHQvLyBMb2NhbC1zY29wZSB3YWxrIChpbnN0cnVtZW50YXRpb24gd2Fsa2VyIFBoYXNlIDIpOiBmdW5jdGlvbi9tZXRob2QvYXJyb3dcblx0Ly8gc2NvcGVzIG9ubHkgKG5vIGJsb2NrIHNjb3BlcyDigJQgZGVjaXNpb24gNSksIHZhcmlhYmxlcyB3aXRoIGlzTXV0YWJsZSBhbmRcblx0Ly8gcmVhc3NpZ25tZW50IHNpdGVzIChkZWNpc2lvbiA2KS4gUnVucyBhZnRlciBkZWZpbml0aW9ucyBhcmUga25vd24gc29cblx0Ly8gdmFyaWFibGUgdHlwZVBhdGhzIGNhbiByZXNvbHZlOyBob2xkZXJTY29wZUlkIGlzIGF0dGFjaGVkIHRvIHVzYWdlc1xuXHQvLyBiZWZvcmUgdGhleSBhcmUgd3JpdHRlbi5cblx0Y29uc3Qgc2NvcGVXYWxrZXIgPSBuZXcgTG9jYWxTY29wZVdhbGtlcigpO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRzY29wZVdhbGtlci5hZGRGaWxlKHNvdXJjZUZpbGUpO1xuXHR9XG5cdGNvbnN0IHNjb3BlUmVzb2x2ZXI6IFNjb3BlVHlwZVJlc29sdmVyID0ge1xuXHRcdHJlc29sdmVCeU5hbWUgOiAobmFtZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkID0+IHtcblx0XHRcdGlmIChkZWZpbml0aW9ucy5oYXMobmFtZSkpIHtcblx0XHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0XHR9XG5cdFx0XHRsZXQgZm91bmQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdGZvciAoY29uc3QgWyBmdWxsUGF0aCwgZGVmaW5pdGlvbiBdIG9mIGRlZmluaXRpb25zKSB7XG5cdFx0XHRcdGlmIChkZWZpbml0aW9uLm5hbWUgIT09IG5hbWUpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHQvLyBBbWJpZ3VvdXMgbmFtZSDigJQgbm8gdHlwZSBjaGVja2VyLCBzbyByZWZ1c2UgdG8gZ3Vlc3Ncblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGZvdW5kID0gZnVsbFBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0fSxcblx0XHRoYXNQYXRoIDogKGZ1bGxQYXRoOiBzdHJpbmcpOiBib29sZWFuID0+IHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCk7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0sXG5cdFx0Ly8gVGhlIGFuYWx5emVyJ3Mgb3duIGxvb2t1cCBsYXcsIGFnYWluc3QgdGhlIHNhbWUgY29tcGxldGUgZ3JhcGggdGhlXG5cdFx0Ly8gdXNhZ2VzIHBhc3MgcmVzb2x2ZWQgd2l0aCDigJQgYSBsb29rdXAoKSBpbml0aWFsaXplciB0aGUgYW5hbHl6ZXJcblx0XHQvLyBhY2NlcHRlZCAoZS5nLiBhbiBpbXBvcnRlZCBIb2xkZXIubG9va3VwKCdUb2tlbicpKSBsYW5kcyB0aGUgc2FtZVxuXHRcdC8vIGZ1bGxQYXRoIGluIHNjb3Blcy5qc29uIGluc3RlYWQgb2Ygc3RhcnZpbmcgdGhlIGNyZWF0aW9uLWdyYXBoXG5cdFx0Ly8gYW5jaG9ycy4gUmVqZWN0ZWQgbG9va3VwcyBzdGF5IHR5cGVQYXRoLWxlc3MgaGVyZTsgdGhlIGFuYWx5emVyXG5cdFx0Ly8gYWxyZWFkeSBoYXJkLWZhaWxlZCB0aGUgcnVuIGFib3ZlLlxuXHRcdHJlc29sdmVMb29rdXAgOiAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQgPT4ge1xuXHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSBhbmFseXplci5yZXNvbHZlTG9va3VwQ2FsbFBhdGgoY2FsbCk7XG5cdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0fSxcblx0fTtcblx0Y29uc3Qgc2NvcGVBbmFseXNpcyA9IHNjb3BlV2Fsa2VyLmJ1aWxkKHNjb3BlUmVzb2x2ZXIpO1xuXHRMb2NhbFNjb3BlV2Fsa2VyLmF0dGFjaEhvbGRlclNjb3BlSWRzKHVzYWdlcywgc2NvcGVXYWxrZXIpO1xuXG5cdGNvbnN0IGRlZmluaXRpb25zUGF0aCA9IHdyaXRlci53cml0ZURlZmluaXRpb25zRmlsZShkZWZpbml0aW9ucyk7XG5cdGNvbnN0IHVzYWdlc1BhdGggPSB3cml0ZXIud3JpdGVVc2FnZXNGaWxlKHVzYWdlcyk7XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgZGVmaW5pdGlvbnMuanNvbiBhdDogJHtkZWZpbml0aW9uc1BhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCB1c2FnZXMuanNvbiBhdDogJHt1c2FnZXNQYXRofWApO1xuXHR9XG5cblx0Ly8gRGV0ZXJtaW5lIEVEUyBzZXR0aW5nOiBleHBsaWNpdCBmbGFnID4gYXV0by1kZXRlY3QgZGl2ZSA+IGRlZmF1bHQgb2ZmXG5cdGxldCBlbmFibGVFRFMgPSBvcHRpb25zLmVkcztcblx0aWYgKGVuYWJsZUVEUyA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0ZW5hYmxlRURTID0gaGFzRGl2ZURlcGVuZGVuY3kocHJvamVjdERpcik7XG5cdH1cblxuXHRpZiAoZW5hYmxlRURTKSB7XG5cdFx0Y29uc3QgZWRzID0gYW5hbHl6ZXIuZ2V0RURTVXNhZ2VzKCk7XG5cdFx0YXR0YWNoV3JhcEpvaW5EYXRhKGVkcywgc2NvcGVXYWxrZXIsIHNjb3BlQW5hbHlzaXMpO1xuXHRcdGNvbnN0IGVkc1BhdGggPSB3cml0ZXIud3JpdGVFRFNGaWxlKGVkcyk7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBlZHMuanNvbiBhdDogJHtlZHNQYXRofWApO1xuXHRcdH1cblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBmbG93Lmpzb24gKG5hdGl2ZSBpbnN0YW5jZSB1c2FnZSB0cmFja2luZylcblx0Y29uc3QgZmxvdyA9IGFuYWx5emVyLmdldEZsb3dVc2FnZXMoKTtcblx0Y29uc3QgZmxvd1BhdGggPSB3cml0ZXIud3JpdGVGbG93RmlsZShmbG93KTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IGZsb3dDb3VudCA9IEFycmF5LmZyb20oZmxvdy52YWx1ZXMoKSkucmVkdWNlKChzdW0sIGFycikgPT4gc3VtICsgYXJyLmxlbmd0aCwgMCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBmbG93Lmpzb24gYXQ6ICR7Zmxvd1BhdGh9ICgke2Zsb3dDb3VudH0gZmxvdyBlbnRyaWVzKWApO1xuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIG1vZHVsZXMuanNvbiAobW9kdWxlLXNjb3BlIGdyYXBoOiBpbXBvcnRzL2V4cG9ydHMsXG5cdC8vIGRlcGVuZGVuY2llcywgY3ljbGVzLCBjcm9zcy1tb2R1bGUgbW5lbW9uaWNhLXR5cGUgZWRnZXMpXG5cdGNvbnN0IGRlZmluZWRUeXBlc0J5RmlsZSA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCBkZWZpbml0aW9uIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRjb25zdCB7IGxvY2F0aW9uIH0gPSBkZWZpbml0aW9uO1xuXHRcdGNvbnN0IGxhc3RDb2xvbiA9IGxvY2F0aW9uLmxhc3RJbmRleE9mKCc6Jyk7XG5cdFx0Y29uc3QgcHJldkNvbG9uID0gbG9jYXRpb24ubGFzdEluZGV4T2YoJzonLCBsYXN0Q29sb24gLSAxKTtcblx0XHRjb25zdCBmaWxlID0gbG9jYXRpb24uc2xpY2UoMCwgcHJldkNvbG9uKTtcblx0XHRjb25zdCBsaXN0ID0gZGVmaW5lZFR5cGVzQnlGaWxlLmdldChmaWxlKSA/PyBbXTtcblx0XHRsaXN0LnB1c2goZnVsbFBhdGgpO1xuXHRcdGRlZmluZWRUeXBlc0J5RmlsZS5zZXQoZmlsZSwgbGlzdCk7XG5cdH1cblx0Y29uc3QgbW9kdWxlR3JhcGggPSBtb2R1bGVHcmFwaEJ1aWxkZXIuYnVpbGQoZGVmaW5lZFR5cGVzQnlGaWxlKTtcblx0Y29uc3QgbW9kdWxlc1BhdGggPSB3cml0ZXIud3JpdGVNb2R1bGVzRmlsZShtb2R1bGVHcmFwaCk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBtb2R1bGVDb3VudCA9IG1vZHVsZUdyYXBoLm1vZHVsZXMuc2l6ZTtcblx0XHRjb25zdCBlZGdlQ291bnQgPSBtb2R1bGVHcmFwaC5lZGdlcy5sZW5ndGg7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBtb2R1bGVzLmpzb24gYXQ6ICR7bW9kdWxlc1BhdGh9ICgke21vZHVsZUNvdW50fSBtb2R1bGVzLCAke2VkZ2VDb3VudH0gZWRnZXMpYCk7XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgc2NvcGVzLmpzb24gKGxvY2FsLXNjb3BlIHdhbGtlcjogc2NvcGVzLCB2YXJpYWJsZXMsXG5cdC8vIHJlYXNzaWdubWVudCBmbG93LXRlcm1pbmF0aW9uIHBvaW50cylcblx0Y29uc3Qgc2NvcGVzUGF0aCA9IHdyaXRlci53cml0ZVNjb3Blc0ZpbGUoc2NvcGVBbmFseXNpcyk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBzY29wZUNvdW50ID0gc2NvcGVBbmFseXNpcy5zY29wZXMuc2l6ZTtcblx0XHRjb25zdCB2YXJpYWJsZUNvdW50ID0gc2NvcGVBbmFseXNpcy52YXJpYWJsZXMuc2l6ZTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHNjb3Blcy5qc29uIGF0OiAke3Njb3Blc1BhdGh9ICgke3Njb3BlQ291bnR9IHNjb3BlcywgJHt2YXJpYWJsZUNvdW50fSB2YXJpYWJsZXMpYCk7XG5cdH1cblxuXHQvLyBUaGUgaW5zaWRlLW91dCBjcmVhdGlvbiB3YWxrIChpbnN0cnVtZW50YXRpb24gd2Fsa2VyIFBoYXNlIDMpOiBhbmNob3JzXG5cdC8vIGFyZSB0aGUgaW5zdGFudGlhdGlvbiB1c2FnZXM7IGNhbGxlcnMgYXJlIGZvbGxvd2VkIHNhbWUtZmlsZSBhbmRcblx0Ly8gY3Jvc3MtZmlsZSAobW9kdWxlIGdyYXBoLCBiYXJyZWxzIGNoYXNlZCkgdW50aWwgb25seSBzdGFydGVycyByZW1haW4uXG5cdGNvbnN0IHNvdXJjZUZpbGVzQnlQYXRoID0gbmV3IE1hcDxzdHJpbmcsIHRzLlNvdXJjZUZpbGU+KCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdHNvdXJjZUZpbGVzQnlQYXRoLnNldChwYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSksIHNvdXJjZUZpbGUpO1xuXHR9XG5cdGNvbnN0IGNyZWF0aW9uR3JhcGhCdWlsZGVyID0gbmV3IENyZWF0aW9uR3JhcGhCdWlsZGVyKG1vZHVsZUdyYXBoLCBzY29wZUFuYWx5c2lzLCBzY29wZVdhbGtlciwgc291cmNlRmlsZXNCeVBhdGgpO1xuXHRjb25zdCBjcmVhdGlvbkdyYXBoID0gY3JlYXRpb25HcmFwaEJ1aWxkZXIuYnVpbGQodXNhZ2VzKTtcblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgaW5zdHJ1bWVudGF0aW9uLmpzb24gKGZyYW1ld29yayBsaWZlY3ljbGUgY3Jvc3Nyb2Fkc1xuXHQvLyBmcm9tIHRoZSBsb2FkZWQgcGx1Z2lucyDigJQgc3ludGFjdGljIGRldGVjdGlvbiBuZWVkcyBubyBkaXZlXG5cdC8vIGRlcGVuZGVuY3ksIHVubGlrZSBlZHMuanNvbikuIHYyIGNhcnJpZXMgdGhlIGNyZWF0aW9uIGdyYXBoXG5cdC8vIGFsb25nc2lkZSB0aGUgcG9pbnRzLlxuXHRjb25zdCBpbnN0cnVtZW50YXRpb24gPSBhbmFseXplci5nZXRJbnN0cnVtZW50YXRpb25Qb2ludHMoKTtcblx0Y29uc3QgaW5zdHJ1bWVudGF0aW9uUGF0aCA9IHdyaXRlci53cml0ZUluc3RydW1lbnRhdGlvbkZpbGUoaW5zdHJ1bWVudGF0aW9uLCBjcmVhdGlvbkdyYXBoKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IG5vZGVDb3VudCA9IGNyZWF0aW9uR3JhcGgubm9kZXMubGVuZ3RoO1xuXHRcdGNvbnN0IGVkZ2VDb3VudCA9IGNyZWF0aW9uR3JhcGguZWRnZXMubGVuZ3RoO1xuXHRcdGNvbnN0IGFuY2hvckNvdW50ID0gY3JlYXRpb25HcmFwaC5hbmNob3JzLmxlbmd0aDtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGluc3RydW1lbnRhdGlvbi5qc29uIGF0OiAke2luc3RydW1lbnRhdGlvblBhdGh9ICgke2luc3RydW1lbnRhdGlvbi5sZW5ndGh9IHBvaW50cylgKTtcblx0XHRjb25zb2xlLmxvZyhgICBjcmVhdGlvbiBncmFwaDogJHtub2RlQ291bnR9IG5vZGVzLCAke2VkZ2VDb3VudH0gZWRnZXMsICR7YW5jaG9yQ291bnR9IGFuY2hvcnNgKTtcblx0fVxuXG5cdC8vIEdlbmVyYXRlIGhpZXJhcmNoeS5qc29uIChzdHJ1Y3R1cmVkKSBhbmQgaGllcmFyY2h5LnR4dCAoQVNDSUkgdHJlZSkgZm9yIHRoZSBUcmllXG5cdGNvbnN0IGhpZXJhcmNoeVJvb3RzID0gZ3JhcGgudG9IaWVyYXJjaHkoKTtcblx0Y29uc3QgaGllcmFyY2h5SnNvblBhdGggPSB3cml0ZXIud3JpdGVIaWVyYXJjaHlGaWxlKGhpZXJhcmNoeVJvb3RzKTtcblx0Y29uc3QgaGllcmFyY2h5VGV4dCA9IHJlbmRlclR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHRjb25zdCBoaWVyYXJjaHlUeHRQYXRoID0gd3JpdGVyLndyaXRlVG8oJ2hpZXJhcmNoeS50eHQnLCBoaWVyYXJjaHlUZXh0KTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaGllcmFyY2h5Lmpzb24gYXQ6ICR7aGllcmFyY2h5SnNvblBhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBoaWVyYXJjaHkudHh0IGF0OiAke2hpZXJhcmNoeVR4dFBhdGh9YCk7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCB0eXBlcyBhdDogJHtvdXRwdXRQYXRofWApO1xuXHRcdGNvbnNvbGUubG9nKGBNb2RlOiAke3VzZU1vZHVsZUF1Z21lbnRhdGlvbiA/ICdnbG9iYWwgYXVnbWVudGF0aW9uIChsZWdhY3kpJyA6ICd0eXBlcyBmaWxlIChkZWZhdWx0KSd9YCk7XG5cdFx0Y29uc29sZS5sb2coYEZvdW5kICR7Z2VuZXJhdGVkVHlwZXMudHlwZXMubGVuZ3RofSB0eXBlczpgKTtcblx0XHRwcmludFR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHR9IGVsc2Uge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgJHtnZW5lcmF0ZWRUeXBlcy50eXBlcy5sZW5ndGh9IHR5cGVzIGF0ICR7b3B0aW9ucy5vdXRwdXREaXIgfHwgJy50YWN0aWNhJ31gKTtcblx0XHRpZiAodXNlTW9kdWxlQXVnbWVudGF0aW9uKSB7XG5cdFx0XHRjb25zb2xlLmxvZygnVXNpbmcgZ2xvYmFsIGF1Z21lbnRhdGlvbiBtb2RlIChsZWdhY3ksIHVzZSBkZWZhdWx0IG1vZGUgZm9yIHR5cGVzLnRzIG9ubHkpJyk7XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIDA7XG59XG5cbi8qKlxuICogV2F0Y2ggbW9kZVxuICovXG5mdW5jdGlvbiB3YXRjaCAob3B0aW9uczogQ0xJT3B0aW9ucyk6IHZvaWQge1xuXHRjb25zb2xlLmxvZygnU3RhcnRpbmcgd2F0Y2ggbW9kZS4uLicpO1xuXG5cdC8vIEluaXRpYWwgcnVuXG5cdHJ1bihvcHRpb25zKTtcblxuXHQvLyBTZXQgdXAgZmlsZSB3YXRjaGluZ1xuXHRjb25zdCBjaG9raWRhciA9IHJlcXVpcmUoJ2Nob2tpZGFyJyk7XG5cdGNvbnN0IHRzY29uZmlnUGF0aCA9IGZpbmRUc0NvbmZpZyhvcHRpb25zLnByb2plY3QpO1xuXG5cdGlmICghdHNjb25maWdQYXRoKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6IENvdWxkIG5vdCBmaW5kIHRzY29uZmlnLmpzb24nKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cblxuXHRjb25zdCBwcm9qZWN0RGlyID0gcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCk7XG5cdGNvbnN0IHdhdGNoUGF0aHMgPSBvcHRpb25zLmluY2x1ZGUgfHwgWyAnKiovKi50cycgXTtcblx0Y29uc3QgaWdub3JlUGF0aHMgPSBvcHRpb25zLmV4Y2x1ZGUgfHwgWyAnKiovKi5kLnRzJywgJ25vZGVfbW9kdWxlcy8qKicsICcudGFjdGljYS8qKicgXTtcblxuXHRjb25zdCB3YXRjaGVyID0gY2hva2lkYXIud2F0Y2god2F0Y2hQYXRocywge1xuXHRcdGN3ZCAgICAgICAgOiBwcm9qZWN0RGlyLFxuXHRcdGlnbm9yZWQgICAgOiBpZ25vcmVQYXRocyxcblx0XHRwZXJzaXN0ZW50IDogdHJ1ZSxcblx0fSk7XG5cblx0d2F0Y2hlci5vbignY2hhbmdlJywgKGZpbGVQYXRoOiBzdHJpbmcpID0+IHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgRmlsZSBjaGFuZ2VkOiAke2ZpbGVQYXRofWApO1xuXHRcdH1cblx0XHRydW4ob3B0aW9ucyk7XG5cdH0pO1xuXG5cdHdhdGNoZXIub24oJ2FkZCcsIChmaWxlUGF0aDogc3RyaW5nKSA9PiB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEZpbGUgYWRkZWQ6ICR7ZmlsZVBhdGh9YCk7XG5cdFx0fVxuXHRcdHJ1bihvcHRpb25zKTtcblx0fSk7XG5cblx0Y29uc29sZS5sb2coJ1dhdGNoaW5nIGZvciBjaGFuZ2VzLi4uIChQcmVzcyBDdHJsK0MgdG8gc3RvcCknKTtcbn1cblxuLyoqXG4gKiBNYWluIGVudHJ5IHBvaW50XG4gKi9cbmZ1bmN0aW9uIG1haW4gKCk6IHZvaWQge1xuXHRjb25zdCBhcmdzID0gcHJvY2Vzcy5hcmd2LnNsaWNlKDIpO1xuXHRjb25zdCBvcHRpb25zID0gcGFyc2VBcmdzKGFyZ3MpO1xuXG5cdGlmIChvcHRpb25zLmhlbHApIHtcblx0XHRwcmludEhlbHAoKTtcblx0XHRwcm9jZXNzLmV4aXQoMCk7XG5cdH1cblxuXHR0cnkge1xuXHRcdGlmIChvcHRpb25zLndhdGNoKSB7XG5cdFx0XHR3YXRjaChvcHRpb25zKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Y29uc3QgY29kZSA9IHJ1bihvcHRpb25zKTtcblx0XHRcdGlmIChjb2RlKSB7XG5cdFx0XHRcdHByb2Nlc3MuZXhpdChjb2RlKTtcblx0XHRcdH1cblx0XHR9XG5cdH0gY2F0Y2ggKGVycm9yKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6JywgZXJyb3IgaW5zdGFuY2VvZiBFcnJvciA/IGVycm9yLm1lc3NhZ2UgOiBlcnJvcik7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG59XG5cbi8vIFJ1biBpZiBleGVjdXRlZCBkaXJlY3RseVxuaWYgKHJlcXVpcmUubWFpbiA9PT0gbW9kdWxlKSB7XG5cdG1haW4oKTtcbn1cblxuZXhwb3J0IHtcblx0bWFpbiwgcnVuLCB3YXRjaCwgcGFyc2VBcmdzIFxufTtcbiJdfQ==