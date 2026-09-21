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
    // Tactica analyzes with its own bundled TypeScript, which may be newer
    // than the compiler the user's tsconfig was written for (e.g. a TS5-era
    // config carrying `baseUrl`, deprecated-errored by TS6's TS5101).
    // Analysis never emits user code, so deprecation errors are about the
    // user's build pipeline, not about analyzability — silence them for the
    // analysis program. Unconditional: a user-pinned older value ('5.0')
    // does not silence 6.0 deprecations and would still fatal below.
    const rawConfig = configFile.config ?? {};
    rawConfig.compilerOptions = {
        ...rawConfig.compilerOptions,
        ignoreDeprecations: '6.0',
    };
    const parsedConfig = ts.parseJsonConfigFileContent(rawConfig, ts.sys, path.dirname(tsconfigPath));
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQWk3Qlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUEvNkI1Qix1Q0FBeUI7QUFDekIsMkNBQTZCO0FBQzdCLG1DQUF1QztBQUN2QywrQ0FBaUM7QUFDakMseUNBQStDO0FBQy9DLCtEQUEyRDtBQUMzRCwyQ0FFcUI7QUFDckIscUNBQXVDO0FBQ3ZDLGlEQUFvRDtBQUNwRCxxREFBd0Q7QUFDeEQscUNBRWtCO0FBQ2xCLG1DQUVpQjtBQTBCakI7O0dBRUc7QUFDSCxTQUFTLFNBQVMsQ0FBRSxJQUFjO0lBQ2pDLE1BQU0sT0FBTyxHQUFlLEVBQUUsQ0FBQztJQUUvQixLQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRSxDQUFDO1FBQ3RDLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBRSxDQUFDLENBQUUsQ0FBQztRQUV0QixRQUFRLEdBQUcsRUFBRSxDQUFDO1lBQ2QsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFNBQVM7Z0JBQ2IsT0FBTyxDQUFDLEtBQUssR0FBRyxJQUFJLENBQUM7Z0JBQ3JCLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssV0FBVztnQkFDZixPQUFPLENBQUMsT0FBTyxHQUFHLElBQUksQ0FBRSxFQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUM5QixNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFVBQVU7Z0JBQ2QsT0FBTyxDQUFDLFNBQVMsR0FBRyxJQUFJLENBQUUsRUFBRSxDQUFDLENBQUUsQ0FBQztnQkFDaEMsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxXQUFX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Q0FBQztnQkFDVixPQUFPLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ3BCLENBQUM7UUFDRixDQUFDO0lBQ0YsQ0FBQztJQUFDLE9BQU8sS0FBSyxFQUFFLENBQUM7UUFDaEIsT0FBTyxDQUFDLEtBQUssQ0FBQyxRQUFRLEVBQUUsS0FBSyxZQUFZLEtBQUssQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLE9BQU8sQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDeEUsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQztJQUNqQixDQUFDO0FBQ0YsQ0FBQztBQUVELDJCQUEyQjtBQUMzQixJQUFJLE9BQU8sQ0FBQyxJQUFJLEtBQUssTUFBTSxFQUFFLENBQUM7SUFDN0IsSUFBSSxFQUFFLENBQUM7QUFDUixDQUFDIiwic291cmNlc0NvbnRlbnQiOlsiIyEvdXNyL2Jpbi9lbnYgbm9kZVxuJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBmcyBmcm9tICdmcyc7XG5pbXBvcnQgKiBhcyBwYXRoIGZyb20gJ3BhdGgnO1xuaW1wb3J0IHsgY3JlYXRlUmVxdWlyZSB9IGZyb20gJ21vZHVsZSc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7IE1uZW1vbmljYUFuYWx5emVyIH0gZnJvbSAnLi9hbmFseXplcic7XG5pbXBvcnQgeyBUb3BvbG9naWNhQW5hbHl6ZXIgfSBmcm9tICcuL3RvcG9sb2dpY2EtYW5hbHl6ZXInO1xuaW1wb3J0IHtcblx0VHlwZXNHZW5lcmF0b3IsIEdyYXBoUmVmZXJlbmNlUmVzb2x2ZXIgXG59IGZyb20gJy4vZ2VuZXJhdG9yJztcbmltcG9ydCB7IFR5cGVzV3JpdGVyIH0gZnJvbSAnLi93cml0ZXInO1xuaW1wb3J0IHsgTW9kdWxlR3JhcGhCdWlsZGVyIH0gZnJvbSAnLi9tb2R1bGUtZ3JhcGgnO1xuaW1wb3J0IHsgQ3JlYXRpb25HcmFwaEJ1aWxkZXIgfSBmcm9tICcuL2NyZWF0aW9uLWdyYXBoJztcbmltcG9ydCB7XG5cdExvY2FsU2NvcGVXYWxrZXIsIFNjb3BlVHlwZVJlc29sdmVyXG59IGZyb20gJy4vc2NvcGVzJztcbmltcG9ydCB7XG5cdHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UsIFR5cGVHcmFwaEltcGwgXG59IGZyb20gJy4vZ3JhcGgnO1xuaW1wb3J0IHtcblx0VGFjdGljYUNvbmZpZywgVHlwZU5vZGUsIEVEU0luZm8sIFNjb3BlQW5hbHlzaXNcbn0gZnJvbSAnLi90eXBlcyc7XG5pbXBvcnQgeyBUYWN0aWNhUGx1Z2luIH0gZnJvbSAnLi9wbHVnaW5zJztcblxuLyoqXG4gKiBDTEkgZW50cnkgcG9pbnQgZm9yIFRhY3RpY2FcbiAqXG4gKiBSdW5zIHRoZSBhbmFseXplciBvdmVyIGEgdHNjb25maWcgcHJvamVjdCBhbmQgd3JpdGVzIC50YWN0aWNhLyBvdXRwdXRcbiAqL1xuXG5pbnRlcmZhY2UgQ0xJT3B0aW9ucyBleHRlbmRzIFRhY3RpY2FDb25maWcge1xuXHR3YXRjaD86IGJvb2xlYW47XG5cdHByb2plY3Q/OiBzdHJpbmc7XG5cdGhlbHA/OiBib29sZWFuO1xuXHQvKiogQ3VzdG9tIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXMgdG8gc2NhbiAqL1xuXHR0b3BvbG9naWNhRGlycz86IHN0cmluZ1tdO1xuXHQvKiogQWRkIC5qcyBleHRlbnNpb25zIHRvIHJlbGF0aXZlIGltcG9ydHMgZm9yIEVTTSBOb2RlTmV4dCByZXNvbHV0aW9uICovXG5cdGVzbT86IGJvb2xlYW47XG5cdC8qKiBFbmFibGUgRURTIChFeGVjdXRpb24gRGF0YSBTdG9yYWdlKSB0cmFja2luZyAqL1xuXHRlZHM/OiBib29sZWFuO1xuXHQvKiogUHJvZ3JhbW1hdGljIHBsdWdpbnM7IGNvbmZpZy1maWxlIHBsdWdpbnMgYXJlIGFwcGVuZGVkIGFmdGVyIHRoZXNlICovXG5cdHBsdWdpbnM/OiBUYWN0aWNhUGx1Z2luW107XG59XG5cbi8qKlxuICogUGFyc2UgY29tbWFuZCBsaW5lIGFyZ3VtZW50c1xuICovXG5mdW5jdGlvbiBwYXJzZUFyZ3MgKGFyZ3M6IHN0cmluZ1tdKTogQ0xJT3B0aW9ucyB7XG5cdGNvbnN0IG9wdGlvbnM6IENMSU9wdGlvbnMgPSB7fTtcblxuXHRmb3IgKGxldCBpID0gMDsgaSA8IGFyZ3MubGVuZ3RoOyBpKyspIHtcblx0XHRjb25zdCBhcmcgPSBhcmdzWyBpIF07XG5cblx0XHRzd2l0Y2ggKGFyZykge1xuXHRcdGNhc2UgJy13Jzpcblx0XHRjYXNlICctLXdhdGNoJzpcblx0XHRcdG9wdGlvbnMud2F0Y2ggPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXAnOlxuXHRcdGNhc2UgJy0tcHJvamVjdCc6XG5cdFx0XHRvcHRpb25zLnByb2plY3QgPSBhcmdzWyArK2kgXTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1vJzpcblx0XHRjYXNlICctLW91dHB1dCc6XG5cdFx0XHRvcHRpb25zLm91dHB1dERpciA9IGFyZ3NbICsraSBdO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLWknOlxuXHRcdGNhc2UgJy0taW5jbHVkZSc6XG5cdFx0XHRvcHRpb25zLmluY2x1ZGUgPSAob3B0aW9ucy5pbmNsdWRlIHx8IFtdKS5jb25jYXQoYXJnc1sgKytpIF0uc3BsaXQoJywnKSk7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctZSc6XG5cdFx0Y2FzZSAnLS1leGNsdWRlJzpcblx0XHRcdG9wdGlvbnMuZXhjbHVkZSA9IChvcHRpb25zLmV4Y2x1ZGUgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1tJzpcblx0XHRjYXNlICctLW1vZHVsZS1hdWdtZW50YXRpb24nOlxuXHRcdFx0b3B0aW9ucy5nbG9iYWxBdWdtZW50YXRpb24gPSBmYWxzZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy12Jzpcblx0XHRjYXNlICctLXZlcmJvc2UnOlxuXHRcdFx0b3B0aW9ucy52ZXJib3NlID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy10Jzpcblx0XHRjYXNlICctLXRvcG9sb2dpY2EnOlxuXHRcdFx0b3B0aW9ucy50b3BvbG9naWNhRGlycyA9IChvcHRpb25zLnRvcG9sb2dpY2FEaXJzIHx8IFtdKS5jb25jYXQoYXJnc1sgKytpIF0uc3BsaXQoJywnKSk7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctLWVzbSc6XG5cdFx0XHRvcHRpb25zLmVzbSA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctLWVkcyc6XG5cdFx0XHRvcHRpb25zLmVkcyA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctLW5vLWVkcyc6XG5cdFx0XHRvcHRpb25zLmVkcyA9IGZhbHNlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLWgnOlxuXHRcdGNhc2UgJy0taGVscCc6XG5cdFx0XHRvcHRpb25zLmhlbHAgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIG9wdGlvbnM7XG59XG5cbi8qKlxuICogUHJpbnQgaGVscCBtZXNzYWdlXG4gKi9cbmZ1bmN0aW9uIHByaW50SGVscCAoKTogdm9pZCB7XG5cdGNvbnNvbGUubG9nKGBcblRhY3RpY2EgLSBUeXBlIGRlZmluaXRpb24gZ2VuZXJhdG9yIGZvciBNbmVtb25pY2FcblxuVXNhZ2U6IHRhY3RpY2EgW29wdGlvbnNdXG5cbk9wdGlvbnM6XG4gIC13LCAtLXdhdGNoICAgICAgICAgICAgICAgV2F0Y2ggZm9yIGZpbGUgY2hhbmdlcyBhbmQgcmVnZW5lcmF0ZSB0eXBlc1xuICAtcCwgLS1wcm9qZWN0ICAgICAgICAgICAgIFBhdGggdG8gdHNjb25maWcuanNvbiAoZGVmYXVsdDogLi90c2NvbmZpZy5qc29uKVxuICAtbywgLS1vdXRwdXQgICAgICAgICAgICAgIE91dHB1dCBkaXJlY3RvcnkgZm9yIGdlbmVyYXRlZCB0eXBlcyAoZGVmYXVsdDogLnRhY3RpY2EpXG4gIC1pLCAtLWluY2x1ZGUgICAgICAgICAgICAgQ29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgZmlsZSBwYXR0ZXJucyB0byBpbmNsdWRlXG4gIC1lLCAtLWV4Y2x1ZGUgICAgICAgICAgICAgQ29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgZmlsZSBwYXR0ZXJucyB0byBleGNsdWRlXG4gIC10LCAtLXRvcG9sb2dpY2EgICAgICAgICAgQ29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgdG9wb2xvZ2ljYSBkaXJlY3RvcmllcyB0byBzY2FuXG4gIC1tLCAtLW1vZHVsZS1hdWdtZW50YXRpb24gVXNlIG1vZHVsZSBhdWdtZW50YXRpb24gaW5zdGVhZCBvZiBnbG9iYWwgKGxlZ2FjeSBtb2RlKVxuICAtLWVzbSAgICAgICAgICAgICAgICAgICAgIEFkZCAuanMgZXh0ZW5zaW9ucyB0byByZWxhdGl2ZSBpbXBvcnRzIChOb2RlTmV4dCBFU00pXG4gIC0tZWRzICAgICAgICAgICAgICAgICAgICAgRW5hYmxlIEVEUyAoRXhlY3V0aW9uIERhdGEgU3RvcmFnZSkgdHJhY2tpbmdcbiAgLS1uby1lZHMgICAgICAgICAgICAgICAgICBEaXNhYmxlIEVEUyB0cmFja2luZ1xuICAtdiwgLS12ZXJib3NlICAgICAgICAgICAgIEVuYWJsZSB2ZXJib3NlIGxvZ2dpbmdcbiAgLWgsIC0taGVscCAgICAgICAgICAgICAgICBTaG93IHRoaXMgaGVscCBtZXNzYWdlXG5cbkNvbmZpZ3VyYXRpb246XG4gIEZyYW1ld29yayBpbnN0cnVtZW50YXRpb24gdm9jYWJ1bGFyeSBpcyBzdXBwbGllZCBieSBwbHVnaW5zLiBQbGFjZSBhXG4gIC50YWN0aWNhLmpzIChvciB0YWN0aWNhLmNvbmZpZy5qcykgbmV4dCB0byB5b3VyIHRzY29uZmlnLmpzb246XG5cbiAgICAgIG1vZHVsZS5leHBvcnRzID0geyBwbHVnaW5zOiBbICd5b3VyLWZyYW1ld29yay1hZGFwdGVyL3RhY3RpY2EnIF0gfTtcblxuICBFbnRyaWVzIGFyZSBtb2R1bGUgc3BlY2lmaWVycyAocmVxdWlyZWQgcmVsYXRpdmUgdG8gdGhlIGNvbmZpZyBmaWxlKSBvclxuICBpbmxpbmUgcGx1Z2luIG9iamVjdHMuIFdpdGhvdXQgcGx1Z2lucywgaW5zdHJ1bWVudGF0aW9uLmpzb24gcG9pbnRzID0gW10uXG5cbkV4YW1wbGVzOlxuICB0YWN0aWNhICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIyBHZW5lcmF0ZSB0eXBlcyB3aXRoIGdsb2JhbCBhdWdtZW50YXRpb24gKGRlZmF1bHQpXG4gIHRhY3RpY2EgLS13YXRjaCAgICAgICAgICAgICAgICAgICAgICAjIFdhdGNoIG1vZGVcbiAgdGFjdGljYSAtLW1vZHVsZS1hdWdtZW50YXRpb24gICAgICAgICMgVXNlIGxlZ2FjeSBtb2R1bGUgYXVnbWVudGF0aW9uIG1vZGVcbiAgdGFjdGljYSAtLXByb2plY3QgLi9zcmMvdHNjb25maWcuanNvbiAjIEN1c3RvbSB0c2NvbmZpZyBwYXRoXG4gIHRhY3RpY2EgLS1vdXRwdXQgLi90eXBlcy9tbmVtb25pY2EgICAjIEN1c3RvbSBvdXRwdXQgZGlyZWN0b3J5XG4gIHRhY3RpY2EgLS10b3BvbG9naWNhIC4vc3JjL2FpLXR5cGVzICAjIFNjYW4gc3BlY2lmaWMgdG9wb2xvZ2ljYSBkaXJlY3RvcnlcbmApO1xufVxuXG4vKipcbiAqIEZpbmQgdHNjb25maWcuanNvblxuICovXG5mdW5jdGlvbiBmaW5kVHNDb25maWcgKHByb2plY3RQYXRoPzogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0aWYgKHByb2plY3RQYXRoKSB7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmMocHJvamVjdFBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gcHJvamVjdFBhdGg7XG5cdFx0fVxuXHRcdHRocm93IG5ldyBFcnJvcihgUHJvamVjdCBmaWxlIG5vdCBmb3VuZDogJHtwcm9qZWN0UGF0aH1gKTtcblx0fVxuXG5cdC8vIExvb2sgZm9yIHRzY29uZmlnLmpzb24gaW4gY3VycmVudCBkaXJlY3RvcnkgYW5kIHBhcmVudCBkaXJlY3Rvcmllc1xuXHRsZXQgY3VycmVudERpciA9IHByb2Nlc3MuY3dkKCk7XG5cdHdoaWxlIChjdXJyZW50RGlyICE9PSBwYXRoLmRpcm5hbWUoY3VycmVudERpcikpIHtcblx0XHRjb25zdCB0c2NvbmZpZ1BhdGggPSBwYXRoLmpvaW4oY3VycmVudERpciwgJ3RzY29uZmlnLmpzb24nKTtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyh0c2NvbmZpZ1BhdGgpKSB7XG5cdFx0XHRyZXR1cm4gdHNjb25maWdQYXRoO1xuXHRcdH1cblx0XHRjdXJyZW50RGlyID0gcGF0aC5kaXJuYW1lKGN1cnJlbnREaXIpO1xuXHR9XG5cblx0cmV0dXJuIHVuZGVmaW5lZDtcbn1cblxuLyoqXG4gKiBMb2FkIFR5cGVTY3JpcHQgcHJvZ3JhbSBmcm9tIHRzY29uZmlnXG4gKi9cbmZ1bmN0aW9uIGxvYWRQcm9ncmFtICh0c2NvbmZpZ1BhdGg6IHN0cmluZyk6IHRzLlByb2dyYW0ge1xuXHRjb25zdCBjb25maWdGaWxlID0gdHMucmVhZENvbmZpZ0ZpbGUodHNjb25maWdQYXRoLCB0cy5zeXMucmVhZEZpbGUpO1xuXG5cdGlmIChjb25maWdGaWxlLmVycm9yKSB7XG5cdFx0Y29uc3QgZXJyb3JUZXh0ID0gdHMuZmxhdHRlbkRpYWdub3N0aWNNZXNzYWdlVGV4dChcblx0XHRcdGNvbmZpZ0ZpbGUuZXJyb3IubWVzc2FnZVRleHQsXG5cdFx0XHQnXFxuJ1xuXHRcdCk7XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBFcnJvciByZWFkaW5nIHRzY29uZmlnOiAke2Vycm9yVGV4dH1gKTtcblx0fVxuXG5cdC8vIFRhY3RpY2EgYW5hbHl6ZXMgd2l0aCBpdHMgb3duIGJ1bmRsZWQgVHlwZVNjcmlwdCwgd2hpY2ggbWF5IGJlIG5ld2VyXG5cdC8vIHRoYW4gdGhlIGNvbXBpbGVyIHRoZSB1c2VyJ3MgdHNjb25maWcgd2FzIHdyaXR0ZW4gZm9yIChlLmcuIGEgVFM1LWVyYVxuXHQvLyBjb25maWcgY2FycnlpbmcgYGJhc2VVcmxgLCBkZXByZWNhdGVkLWVycm9yZWQgYnkgVFM2J3MgVFM1MTAxKS5cblx0Ly8gQW5hbHlzaXMgbmV2ZXIgZW1pdHMgdXNlciBjb2RlLCBzbyBkZXByZWNhdGlvbiBlcnJvcnMgYXJlIGFib3V0IHRoZVxuXHQvLyB1c2VyJ3MgYnVpbGQgcGlwZWxpbmUsIG5vdCBhYm91dCBhbmFseXphYmlsaXR5IOKAlCBzaWxlbmNlIHRoZW0gZm9yIHRoZVxuXHQvLyBhbmFseXNpcyBwcm9ncmFtLiBVbmNvbmRpdGlvbmFsOiBhIHVzZXItcGlubmVkIG9sZGVyIHZhbHVlICgnNS4wJylcblx0Ly8gZG9lcyBub3Qgc2lsZW5jZSA2LjAgZGVwcmVjYXRpb25zIGFuZCB3b3VsZCBzdGlsbCBmYXRhbCBiZWxvdy5cblx0Y29uc3QgcmF3Q29uZmlnID0gY29uZmlnRmlsZS5jb25maWcgPz8ge307XG5cdHJhd0NvbmZpZy5jb21waWxlck9wdGlvbnMgPSB7XG5cdFx0Li4ucmF3Q29uZmlnLmNvbXBpbGVyT3B0aW9ucyxcblx0XHRpZ25vcmVEZXByZWNhdGlvbnMgOiAnNi4wJyxcblx0fTtcblxuXHRjb25zdCBwYXJzZWRDb25maWcgPSB0cy5wYXJzZUpzb25Db25maWdGaWxlQ29udGVudChcblx0XHRyYXdDb25maWcsXG5cdFx0dHMuc3lzLFxuXHRcdHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpXG5cdCk7XG5cblx0aWYgKHBhcnNlZENvbmZpZy5lcnJvcnMubGVuZ3RoID4gMCkge1xuXHRcdGNvbnN0IGVycm9yTWVzc2FnZXMgPSBwYXJzZWRDb25maWcuZXJyb3JzLm1hcChlID0+XG5cdFx0XHR0cy5mbGF0dGVuRGlhZ25vc3RpY01lc3NhZ2VUZXh0KGUubWVzc2FnZVRleHQsICdcXG4nKSk7XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBFcnJvciBwYXJzaW5nIHRzY29uZmlnOiAke2Vycm9yTWVzc2FnZXMuam9pbignXFxuJyl9YCk7XG5cdH1cblxuXHRjb25zdCBwcm9ncmFtID0gdHMuY3JlYXRlUHJvZ3JhbSh7XG5cdFx0cm9vdE5hbWVzIDogcGFyc2VkQ29uZmlnLmZpbGVOYW1lcyxcblx0XHRvcHRpb25zICAgOiBwYXJzZWRDb25maWcub3B0aW9ucyxcblx0fSk7XG5cblx0cmV0dXJuIHByb2dyYW07XG59XG5cbi8qKlxuICogTG9vayB1cCBhIHZhcmlhYmxlIGJ5IG5hbWUgc3RhcnRpbmcgZnJvbSBhIHNjb3BlLCB3YWxraW5nIG91dHdhcmQgdGhyb3VnaFxuICogcGFyZW50U2NvcGVJZC4gVGhlIGlubmVybW9zdCBiaW5kaW5nIHdpbnMgZXZlbiB3aGVuIGl0IGNhcnJpZXMgbm8gdHlwZVBhdGhcbiAqIChzaGFkb3dpbmcgaG9uZXN0eSDigJQgYW4gdW50eXBlZCBsb2NhbCBzaGFkb3dzIGEgdHlwZWQgb3V0ZXIgb25lKS5cbiAqL1xuZnVuY3Rpb24gcmVzb2x2ZVNjb3BlZFZhcmlhYmxlVHlwZVBhdGggKFxuXHRuYW1lOiBzdHJpbmcsXG5cdHNjb3BlSWQ6IHN0cmluZyxcblx0c2NvcGVBbmFseXNpczogU2NvcGVBbmFseXNpc1xuKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0bGV0IGN1cnJlbnQ6IHN0cmluZyB8IHVuZGVmaW5lZCA9IHNjb3BlSWQ7XG5cdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0Y29uc3QgdmFyaWFibGUgPSBzY29wZUFuYWx5c2lzLnZhcmlhYmxlcy5nZXQoYCR7Y3VycmVudH0jJHtuYW1lfWApO1xuXHRcdGlmICh2YXJpYWJsZSkge1xuXHRcdFx0Y29uc3QgeyB0eXBlUGF0aCB9ID0gdmFyaWFibGU7XG5cdFx0XHRyZXR1cm4gdHlwZVBhdGg7XG5cdFx0fVxuXHRcdGN1cnJlbnQgPSBzY29wZUFuYWx5c2lzLnNjb3Blcy5nZXQoY3VycmVudCk/LnBhcmVudFNjb3BlSWQ7XG5cdH1cblx0cmV0dXJuIHVuZGVmaW5lZDtcbn1cblxuLyoqXG4gKiBKb2luIGRhdGEgZm9yIG1uZW1vZ3JhcGhpY2EncyB3cmFwcGVycyBsYXllcjogcGluIGVhY2ggd3JhcCBlbnRyeSB0byB0aGVcbiAqIHNjb3BlIGhvbGRpbmcgaXRzIGNhbGwgc2l0ZSwgYW5kIHJlc29sdmUgdGhlIHdyYXBwZWQgaW5zdGFuY2UgYXJndW1lbnQnc1xuICogbW5lbW9uaWNhIHR5cGUgdGhyb3VnaCB0aGUgc2NvcGUtdmFyaWFibGUgY2hhaW4uXG4gKi9cbmZ1bmN0aW9uIGF0dGFjaFdyYXBKb2luRGF0YSAoXG5cdGVkczogTWFwPHN0cmluZywgRURTSW5mb1tdPixcblx0c2NvcGVXYWxrZXI6IExvY2FsU2NvcGVXYWxrZXIsXG5cdHNjb3BlQW5hbHlzaXM6IFNjb3BlQW5hbHlzaXNcbik6IHZvaWQge1xuXHRmb3IgKGNvbnN0IGVudHJpZXMgb2YgZWRzLnZhbHVlcygpKSB7XG5cdFx0Zm9yIChjb25zdCBlbnRyeSBvZiBlbnRyaWVzKSB7XG5cdFx0XHRpZiAoZW50cnkua2luZCAhPT0gJ3dyYXAnKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgaG9sZGVyU2NvcGVJZCA9IHNjb3BlV2Fsa2VyLmZpbmRIb2xkZXJTY29wZUlkKGVudHJ5LmxvY2F0aW9uKTtcblx0XHRcdGlmICghaG9sZGVyU2NvcGVJZCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGVudHJ5LnNjb3BlSWQgPSBob2xkZXJTY29wZUlkO1xuXHRcdFx0aWYgKCFlbnRyeS5pbnN0YW5jZUFyZykge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHdyYXBzVHlwZVBhdGggPSByZXNvbHZlU2NvcGVkVmFyaWFibGVUeXBlUGF0aChcblx0XHRcdFx0ZW50cnkuaW5zdGFuY2VBcmcsXG5cdFx0XHRcdGhvbGRlclNjb3BlSWQsXG5cdFx0XHRcdHNjb3BlQW5hbHlzaXNcblx0XHRcdCk7XG5cdFx0XHRpZiAod3JhcHNUeXBlUGF0aCkge1xuXHRcdFx0XHRlbnRyeS53cmFwc1R5cGVQYXRoID0gd3JhcHNUeXBlUGF0aDtcblx0XHRcdH1cblx0XHR9XG5cdH1cbn1cblxuLyoqXG4gKiBSZW5kZXIgdHlwZSBoaWVyYXJjaHkgYXMgYW4gQVNDSUkgdHJlZSBzdHJpbmcuXG4gKi9cbmZ1bmN0aW9uIHJlbmRlclR5cGVIaWVyYXJjaHkgKGdyYXBoOiBUeXBlR3JhcGhJbXBsKTogc3RyaW5nIHtcblx0Y29uc3QgbGluZXM6IHN0cmluZ1tdID0gWyAnVHlwZSBIaWVyYXJjaHkgKFRyaWUpOicgXTtcblxuXHRmdW5jdGlvbiByZW5kZXJOb2RlIChub2RlOiBUeXBlTm9kZSwgcHJlZml4ID0gJycsIGlzTGFzdCA9IHRydWUpOiB2b2lkIHtcblx0XHRjb25zdCBjb25uZWN0b3IgPSBpc0xhc3QgPyAn4pSU4pSA4pSAICcgOiAn4pSc4pSA4pSAICc7XG5cdFx0Ly8gVXNlIG5vZGUuZnVsbFBhdGggZGlyZWN0bHkgYW5kIGNvbnZlcnQgZG90cyB0byB1bmRlcnNjb3Jlc1xuXHRcdGNvbnN0IGluc3RhbmNlTmFtZSA9IG5vZGUuZnVsbFBhdGgucmVwbGFjZSgvXFwuL2csICdfJyk7XG5cdFx0bGluZXMucHVzaChgJHtwcmVmaXh9JHtjb25uZWN0b3J9JHtpbnN0YW5jZU5hbWV9YCk7XG5cblx0XHRjb25zdCBjaGlsZHJlbiA9IEFycmF5LmZyb20obm9kZS5jaGlsZHJlbi52YWx1ZXMoKSk7XG5cdFx0Y29uc3QgbmV3UHJlZml4ID0gcHJlZml4ICsgKGlzTGFzdCA/ICcgICAgJyA6ICfilIIgICAnKTtcblxuXHRcdGZvciAobGV0IGkgPSAwOyBpIDwgY2hpbGRyZW4ubGVuZ3RoOyBpKyspIHtcblx0XHRcdHJlbmRlck5vZGUoY2hpbGRyZW5bIGkgXSwgbmV3UHJlZml4LCBpID09PSBjaGlsZHJlbi5sZW5ndGggLSAxKTtcblx0XHR9XG5cdH1cblxuXHRjb25zdCByb290cyA9IEFycmF5LmZyb20oZ3JhcGgucm9vdHMudmFsdWVzKCkpO1xuXHRmb3IgKGxldCBpID0gMDsgaSA8IHJvb3RzLmxlbmd0aDsgaSsrKSB7XG5cdFx0cmVuZGVyTm9kZShyb290c1sgaSBdLCAnJywgaSA9PT0gcm9vdHMubGVuZ3RoIC0gMSk7XG5cdH1cblx0Ly8gRW1wdHkgbGluZSBhdCBlbmRcblx0bGluZXMucHVzaCgnJyk7XG5cblx0Y29uc3QgcmVzdWx0ID0gbGluZXMuam9pbignXFxuJyk7XG5cdHJldHVybiByZXN1bHQ7XG59XG5cbi8qKlxuICogUHJpbnQgdHlwZSBoaWVyYXJjaHkgdG8gdGhlIGNvbnNvbGUuXG4gKi9cbmZ1bmN0aW9uIHByaW50VHlwZUhpZXJhcmNoeSAoZ3JhcGg6IFR5cGVHcmFwaEltcGwpOiB2b2lkIHtcblx0Y29uc3Qgb3V0cHV0ID0gcmVuZGVyVHlwZUhpZXJhcmNoeShncmFwaCk7XG5cdGNvbnNvbGUubG9nKG91dHB1dCk7XG59XG5cbi8qKlxuICogQ2hlY2sgaWYgQG1uZW1vbmljYS9kaXZlIGlzIHByZXNlbnQgaW4gcGFja2FnZS5qc29uIGRlcGVuZGVuY2llc1xuICovXG5mdW5jdGlvbiBoYXNEaXZlRGVwZW5kZW5jeSAocHJvamVjdERpcjogc3RyaW5nKTogYm9vbGVhbiB7XG5cdGNvbnN0IHBhY2thZ2VKc29uUGF0aCA9IHBhdGguam9pbihwcm9qZWN0RGlyLCAncGFja2FnZS5qc29uJyk7XG5cdGlmICghZnMuZXhpc3RzU3luYyhwYWNrYWdlSnNvblBhdGgpKSB7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cdHRyeSB7XG5cdFx0Y29uc3QgY29udGVudCA9IGZzLnJlYWRGaWxlU3luYyhwYWNrYWdlSnNvblBhdGgsICd1dGYtOCcpO1xuXHRcdGNvbnN0IHBrZyA9IEpTT04ucGFyc2UoY29udGVudCk7XG5cdFx0Y29uc3QgZGVwcyA9IHBrZy5kZXBlbmRlbmNpZXMgfHwge307XG5cdFx0Y29uc3QgZGV2RGVwcyA9IHBrZy5kZXZEZXBlbmRlbmNpZXMgfHwge307XG5cdFx0Y29uc3QgcGVlckRlcHMgPSBwa2cucGVlckRlcGVuZGVuY2llcyB8fCB7fTtcblx0XHRyZXR1cm4gJ0BtbmVtb25pY2EvZGl2ZScgaW4gZGVwcyB8fCAnQG1uZW1vbmljYS9kaXZlJyBpbiBkZXZEZXBzIHx8ICdAbW5lbW9uaWNhL2RpdmUnIGluIHBlZXJEZXBzO1xuXHR9IGNhdGNoIHtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cbn1cblxuLyoqXG4gKiBTY2FuIGZvciB0b3BvbG9naWNhIGRpcmVjdG9yeSBzdHJ1Y3R1cmVzXG4gKi9cbmZ1bmN0aW9uIHNjYW5Ub3BvbG9naWNhRGlyZWN0b3JpZXMgKHByb2plY3REaXI6IHN0cmluZywgY3VzdG9tRGlycz86IHN0cmluZ1tdKTogc3RyaW5nW10ge1xuXHRjb25zdCBkaXJzOiBzdHJpbmdbXSA9IFtdO1xuXG5cdC8vIEZpcnN0LCBhZGQgY3VzdG9tIGRpcmVjdG9yaWVzIGlmIHNwZWNpZmllZFxuXHRpZiAoY3VzdG9tRGlycykge1xuXHRcdGZvciAoY29uc3QgZGlyIG9mIGN1c3RvbURpcnMpIHtcblx0XHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmlzQWJzb2x1dGUoZGlyKSA/IGRpciA6IHBhdGguam9pbihwcm9qZWN0RGlyLCBkaXIpO1xuXHRcdFx0aWYgKGZzLmV4aXN0c1N5bmMoZGlyUGF0aCkgJiYgZnMuc3RhdFN5bmMoZGlyUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb25zb2xlLndhcm4oYFdhcm5pbmc6IFRvcG9sb2dpY2EgZGlyZWN0b3J5IG5vdCBmb3VuZDogJHtkaXJQYXRofWApO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8vIFRoZW4gYXV0by1kaXNjb3ZlciBzdGFuZGFyZCB0b3BvbG9naWNhIGRpcmVjdG9yaWVzXG5cdGNvbnN0IHBvc3NpYmxlRGlycyA9IFsgJ2FpLXR5cGVzJywgJ3R5cGVzJywgJ3RvcG9sb2dpY2EtdHlwZXMnIF07XG5cblx0Zm9yIChjb25zdCBkaXJOYW1lIG9mIHBvc3NpYmxlRGlycykge1xuXHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgZGlyTmFtZSk7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmMoZGlyUGF0aCkgJiYgZnMuc3RhdFN5bmMoZGlyUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0Ly8gQXZvaWQgZHVwbGljYXRlc1xuXHRcdFx0aWYgKCFkaXJzLmluY2x1ZGVzKGRpclBhdGgpKSB7XG5cdFx0XHRcdGRpcnMucHVzaChkaXJQYXRoKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvLyBBbHNvIHNjYW4gc3JjLyBzdWJkaXJlY3Rvcnlcblx0Y29uc3Qgc3JjUGF0aCA9IHBhdGguam9pbihwcm9qZWN0RGlyLCAnc3JjJyk7XG5cdGlmIChmcy5leGlzdHNTeW5jKHNyY1BhdGgpICYmIGZzLnN0YXRTeW5jKHNyY1BhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRmb3IgKGNvbnN0IGRpck5hbWUgb2YgcG9zc2libGVEaXJzKSB7XG5cdFx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5qb2luKHNyY1BhdGgsIGRpck5hbWUpO1xuXHRcdFx0aWYgKGZzLmV4aXN0c1N5bmMoZGlyUGF0aCkgJiYgZnMuc3RhdFN5bmMoZGlyUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0XHQvLyBBdm9pZCBkdXBsaWNhdGVzXG5cdFx0XHRcdGlmICghZGlycy5pbmNsdWRlcyhkaXJQYXRoKSkge1xuXHRcdFx0XHRcdGRpcnMucHVzaChkaXJQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdHJldHVybiBkaXJzO1xufVxuXG4vKipcbiAqIENvbmZpZyBmaWxlIGNhbmRpZGF0ZXMgKGVzbGludC1zdHlsZSBwcm9qZWN0IGNvbmZpZyksIHNlYXJjaGVkIG5leHQgdG9cbiAqIHRoZSByZXNvbHZlZCB0c2NvbmZpZyBmaXJzdCwgdGhlbiBpbiB0aGUgY3VycmVudCB3b3JraW5nIGRpcmVjdG9yeS5cbiAqL1xuY29uc3QgQ09ORklHX0ZJTEVfTkFNRVMgPSBbICcudGFjdGljYS5qcycsICd0YWN0aWNhLmNvbmZpZy5qcycgXTtcblxuaW50ZXJmYWNlIFRhY3RpY2FDb25maWdGaWxlIHtcblx0cGx1Z2lucz86IEFycmF5PFRhY3RpY2FQbHVnaW4gfCBzdHJpbmc+O1xufVxuXG4vKipcbiAqIExvYWQgZnJhbWV3b3JrLXZvY2FidWxhcnkgcGx1Z2luczogcHJvZ3JhbW1hdGljIG9wdGlvbnMgZmlyc3QsIHRoZW4gdGhlXG4gKiBwcm9qZWN0IGNvbmZpZyBmaWxlLiBTdHJpbmcgZW50cmllcyBhcmUgbW9kdWxlIHNwZWNpZmllcnMgcmVxdWlyZWRcbiAqIHJlbGF0aXZlIHRvIHRoZSBjb25maWcgZmlsZSAoZS5nLiBhbiBhZGFwdGVyIHBhY2thZ2UncyBwbHVnaW4gc3VicGF0aCkuXG4gKiBXaXRob3V0IGEgY29uZmlnIGZpbGUgYW5kIHdpdGhvdXQgcHJvZ3JhbW1hdGljIHBsdWdpbnMgdGhlIGFuYWx5emVyXG4gKiBzdGF5cyBmcmFtZXdvcmstYmxpbmQgYW5kIGluc3RydW1lbnRhdGlvbi5qc29uIGNhcnJpZXMgZW1wdHkgcG9pbnRzLlxuICovXG5mdW5jdGlvbiBsb2FkVGFjdGljYVBsdWdpbnMgKHByb2plY3REaXI6IHN0cmluZywgb3B0aW9uczogQ0xJT3B0aW9ucyk6IFRhY3RpY2FQbHVnaW5bXSB7XG5cdGNvbnN0IHBsdWdpbnM6IFRhY3RpY2FQbHVnaW5bXSA9IFsgLi4uKG9wdGlvbnMucGx1Z2lucyB8fCBbXSkgXTtcblxuXHRjb25zdCBzZWFyY2hEaXJzID0gWyBwcm9qZWN0RGlyIF07XG5cdGNvbnN0IGN3ZCA9IHByb2Nlc3MuY3dkKCk7XG5cdGlmIChjd2QgIT09IHByb2plY3REaXIpIHtcblx0XHRzZWFyY2hEaXJzLnB1c2goY3dkKTtcblx0fVxuXG5cdGxldCBjb25maWdQYXRoOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdGZvciAoY29uc3QgZGlyIG9mIHNlYXJjaERpcnMpIHtcblx0XHRmb3IgKGNvbnN0IG5hbWUgb2YgQ09ORklHX0ZJTEVfTkFNRVMpIHtcblx0XHRcdGNvbnN0IGNhbmRpZGF0ZSA9IHBhdGguam9pbihkaXIsIG5hbWUpO1xuXHRcdFx0aWYgKGZzLmV4aXN0c1N5bmMoY2FuZGlkYXRlKSkge1xuXHRcdFx0XHRjb25maWdQYXRoID0gY2FuZGlkYXRlO1xuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKGNvbmZpZ1BhdGgpIHtcblx0XHRcdGJyZWFrO1xuXHRcdH1cblx0fVxuXG5cdGlmICghY29uZmlnUGF0aCkge1xuXHRcdHJldHVybiBwbHVnaW5zO1xuXHR9XG5cblx0Ly8gY3JlYXRlUmVxdWlyZSBhbmNob3JlZCBhdCB0aGUgY29uZmlnIGZpbGU6IHRoZSBjb25maWcncyBvd24gaW1wb3J0c1xuXHQvLyBhbmQgc3RyaW5nIHBsdWdpbiBzcGVjaWZpZXJzIHJlc29sdmUgYWdhaW5zdCB0aGUgcHJvamVjdCdzIG1vZHVsZXNcblx0Y29uc3QgY29uZmlnUmVxdWlyZSA9IGNyZWF0ZVJlcXVpcmUoY29uZmlnUGF0aCk7XG5cdGNvbnN0IGxvYWRlZCA9IGNvbmZpZ1JlcXVpcmUoY29uZmlnUGF0aCk7XG5cdGNvbnN0IGNvbmZpZzogVGFjdGljYUNvbmZpZ0ZpbGUgPSBsb2FkZWQgJiYgdHlwZW9mIGxvYWRlZCA9PT0gJ29iamVjdCcgJiYgJ2RlZmF1bHQnIGluIGxvYWRlZFxuXHRcdD8gbG9hZGVkLmRlZmF1bHRcblx0XHQ6IGxvYWRlZDtcblx0Y29uc3QgZW50cmllcyA9IGNvbmZpZyAmJiBBcnJheS5pc0FycmF5KGNvbmZpZy5wbHVnaW5zKSA/IGNvbmZpZy5wbHVnaW5zIDogW107XG5cblx0Zm9yIChjb25zdCBlbnRyeSBvZiBlbnRyaWVzKSB7XG5cdFx0aWYgKHR5cGVvZiBlbnRyeSAhPT0gJ3N0cmluZycpIHtcblx0XHRcdHBsdWdpbnMucHVzaChlbnRyeSk7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cdFx0Y29uc3QgbW9kID0gY29uZmlnUmVxdWlyZShlbnRyeSk7XG5cdFx0Y29uc3QgcGx1Z2luOiBUYWN0aWNhUGx1Z2luID0gbW9kICYmIHR5cGVvZiBtb2QgPT09ICdvYmplY3QnICYmICdkZWZhdWx0JyBpbiBtb2Rcblx0XHRcdD8gbW9kLmRlZmF1bHRcblx0XHRcdDogbW9kO1xuXHRcdHBsdWdpbnMucHVzaChwbHVnaW4pO1xuXHR9XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IG5hbWVzID0gcGx1Z2lucy5tYXAocGx1Z2luID0+IHBsdWdpbi5uYW1lIHx8ICcodW5uYW1lZCknKS5qb2luKCcsICcpO1xuXHRcdGNvbnNvbGUubG9nKGBMb2FkZWQgdGFjdGljYSBjb25maWc6ICR7Y29uZmlnUGF0aH0gKHBsdWdpbnM6ICR7bmFtZXMgfHwgJ25vbmUnfSlgKTtcblx0fVxuXG5cdHJldHVybiBwbHVnaW5zO1xufVxuXG4vKipcbiAqIFJ1biB0eXBlIGdlbmVyYXRpb24uIFJldHVybnMgMCBvbiBzdWNjZXNzOyAxIHdoZW4gdGhlIGdyYXBoIGlkZW50aXR5IGxhd1xuICogYWJvcnRlZCB0aGUgcnVuIChmYWlsdXJlcyBwcmludGVkLCBubyAudGFjdGljYSBvdXRwdXQgd3JpdHRlbikuXG4gKi9cbmZ1bmN0aW9uIHJ1biAob3B0aW9uczogQ0xJT3B0aW9ucyk6IG51bWJlciB7XG5cdGNvbnN0IHRzY29uZmlnUGF0aCA9IGZpbmRUc0NvbmZpZyhvcHRpb25zLnByb2plY3QpO1xuXG5cdGlmICghdHNjb25maWdQYXRoKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6IENvdWxkIG5vdCBmaW5kIHRzY29uZmlnLmpzb24nKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYFVzaW5nIHRzY29uZmlnOiAke3RzY29uZmlnUGF0aH1gKTtcblx0fVxuXG5cdC8vIEZyYW1ld29yayB2b2NhYnVsYXJ5IGFycml2ZXMgdmlhIHBsdWdpbnMg4oCUIGEgY29uZmlnIGZpbGUgbmV4dCB0byB0aGVcblx0Ly8gdHNjb25maWcgKG9yIGluIGN3ZCkgYW5kL29yIHByb2dyYW1tYXRpYyBvcHRpb25zLiBOb25lIGxvYWRlZCBtZWFuc1xuXHQvLyB0aGUgYW5hbHl6ZXIgZGV0ZWN0cyB6ZXJvIGluc3RydW1lbnRhdGlvbiBwb2ludHMuXG5cdGNvbnN0IHBsdWdpbnMgPSBsb2FkVGFjdGljYVBsdWdpbnMocGF0aC5kaXJuYW1lKHBhdGgucmVzb2x2ZSh0c2NvbmZpZ1BhdGgpKSwgb3B0aW9ucyk7XG5cblx0Ly8gTG9hZCBUeXBlU2NyaXB0IHByb2dyYW1cblx0Y29uc3QgcHJvZ3JhbSA9IGxvYWRQcm9ncmFtKHRzY29uZmlnUGF0aCk7XG5cblx0Ly8gQ3JlYXRlIGFuYWx5emVyXG5cdGNvbnN0IGFuYWx5emVyID0gbmV3IE1uZW1vbmljYUFuYWx5emVyKHByb2dyYW0sIHBsdWdpbnMpO1xuXG5cdC8vIERldGVybWluZSBvdXRwdXQgZGlyZWN0b3J5IGZvciBleGNsdXNpb25cblx0Y29uc3Qgb3V0cHV0RGlyID0gb3B0aW9ucy5vdXRwdXREaXIgfHwgJy50YWN0aWNhJztcblx0Y29uc3Qgb3V0cHV0RGlyUGF0aCA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBvdXRwdXREaXIpO1xuXHQvLyBUaGUgcHJvamVjdC1jb252ZW50aW9uYWwgLnRhY3RpY2EgZGlyIChuZXh0IHRvIHRzY29uZmlnKSBpcyBBTFdBWVNcblx0Ly8gZXhjbHVkZWQsIGV2ZW4gd2hlbiAtLW91dHB1dCBwb2ludHMgZWxzZXdoZXJlOiBnZW5lcmF0ZWQgZmlsZXMgYXJlXG5cdC8vIG5ldmVyIHByb2plY3Qgc291cmNlLiByZXNvbHZlKCkgYm90aCBzaWRlcyDigJQgdHNjb25maWdQYXRoIG1heSBiZVxuXHQvLyByZWxhdGl2ZSAoJy4vdHNjb25maWcuanNvbicpIHdoaWxlIHNvdXJjZUZpbGUuZmlsZU5hbWUgaXMgYWJzb2x1dGVcblx0Y29uc3QgY29udmVudGlvbmFsT3V0cHV0RGlyID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpLCAnLnRhY3RpY2EnKTtcblxuXHQvLyBDb2xsZWN0IHNvdXJjZSBmaWxlcyB0byBhbmFseXplXG5cdGNvbnN0IHNvdXJjZUZpbGVzOiB0cy5Tb3VyY2VGaWxlW10gPSBbXTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHByb2dyYW0uZ2V0U291cmNlRmlsZXMoKSkge1xuXHRcdGlmIChzb3VyY2VGaWxlLmlzRGVjbGFyYXRpb25GaWxlKSB7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cblx0XHRjb25zdCBhYnNvbHV0ZUZpbGVOYW1lID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdGlmIChhYnNvbHV0ZUZpbGVOYW1lLnN0YXJ0c1dpdGgob3V0cHV0RGlyUGF0aCArIHBhdGguc2VwKSB8fFxuXHRcdFx0YWJzb2x1dGVGaWxlTmFtZS5zdGFydHNXaXRoKGNvbnZlbnRpb25hbE91dHB1dERpciArIHBhdGguc2VwKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZXhjbHVkZSBwYXR0ZXJuc1xuXHRcdGlmIChvcHRpb25zLmV4Y2x1ZGUpIHtcblx0XHRcdGNvbnN0IHNob3VsZEV4Y2x1ZGUgPSBvcHRpb25zLmV4Y2x1ZGUuc29tZShwYXR0ZXJuID0+XG5cdFx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUuaW5jbHVkZXMocGF0dGVybi5yZXBsYWNlKC9cXCovZywgJycpKSk7XG5cdFx0XHRpZiAoc2hvdWxkRXhjbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBDaGVjayBpbmNsdWRlIHBhdHRlcm5zXG5cdFx0aWYgKG9wdGlvbnMuaW5jbHVkZSAmJiBvcHRpb25zLmluY2x1ZGUubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3Qgc2hvdWxkSW5jbHVkZSA9IG9wdGlvbnMuaW5jbHVkZS5zb21lKHBhdHRlcm4gPT5cblx0XHRcdFx0c291cmNlRmlsZS5maWxlTmFtZS5pbmNsdWRlcyhwYXR0ZXJuLnJlcGxhY2UoL1xcKi9nLCAnJykpKTtcblx0XHRcdGlmICghc2hvdWxkSW5jbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRzb3VyY2VGaWxlcy5wdXNoKHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0Ly8gU2NhbiBmb3IgdG9wb2xvZ2ljYSBkaXJlY3Rvcnkgc3RydWN0dXJlcyBGSVJTVFxuXHRjb25zdCBwcm9qZWN0RGlyID0gcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCk7XG5cdGNvbnN0IHRvcG9sb2dpY2FEaXJzID0gc2NhblRvcG9sb2dpY2FEaXJlY3Rvcmllcyhwcm9qZWN0RGlyLCBvcHRpb25zLnRvcG9sb2dpY2FEaXJzKTtcblxuXHRpZiAodG9wb2xvZ2ljYURpcnMubGVuZ3RoID4gMCAmJiBvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgRm91bmQgdG9wb2xvZ2ljYSBkaXJlY3RvcmllczogJHt0b3BvbG9naWNhRGlycy5qb2luKCcsICcpfWApO1xuXHR9XG5cblx0Ly8gQW5hbHl6ZSB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIEJFRk9SRSB1c2FnZSBjb2xsZWN0aW9uXG5cdGNvbnN0IHRvcG9sb2dpY2FBbmFseXplciA9IG5ldyBUb3BvbG9naWNhQW5hbHl6ZXIoKTtcblx0Y29uc3QgdG9wb2xvZ2ljYVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIGltcG9ydCgnLi90eXBlcycpLlR5cGVOb2RlPigpO1xuXHRmb3IgKGNvbnN0IGRpciBvZiB0b3BvbG9naWNhRGlycykge1xuXHRcdGNvbnN0IHJlc3VsdCA9IHRvcG9sb2dpY2FBbmFseXplci5hbmFseXplRGlyZWN0b3J5KGRpcik7XG5cdFx0aWYgKHJlc3VsdC50eXBlcy5zaXplID4gMCkge1xuXHRcdFx0Ly8gQ29sbGVjdCB0b3BvbG9naWNhIHR5cGVzIGZvciBkZWZpbml0aW9ucyBhbmQgdXNhZ2UgdHJhY2tpbmdcblx0XHRcdGZvciAoY29uc3QgWyB0eXBlUGF0aCwgbm9kZSBdIG9mIHJlc3VsdC50eXBlcykge1xuXHRcdFx0XHR0b3BvbG9naWNhVHlwZXMuc2V0KHR5cGVQYXRoLCBub2RlKTtcblx0XHRcdH1cblx0XHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdFx0Y29uc29sZS5sb2coYEFkZGVkICR7cmVzdWx0LnR5cGVzLnNpemV9IHR5cGVzIGZyb20gJHtkaXJ9YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChyZXN1bHQuZXJyb3JzLmxlbmd0aCA+IDAgJiYgb3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRyZXN1bHQuZXJyb3JzLmZvckVhY2goZXJyID0+IGNvbnNvbGUud2FybihgW1RvcG9sb2dpY2FdICR7ZXJyfWApKTtcblx0XHR9XG5cdH1cblxuXHQvLyBBZGQgdG9wb2xvZ2ljYSB0eXBlcyB0byBhbmFseXplciBzbyB0aGV5J3JlIGF2YWlsYWJsZSBmb3IgdXNhZ2UgZGV0ZWN0aW9uXG5cdC8vIFByb2Nlc3MgaW4gb3JkZXIgb2YgcGF0aCBkZXB0aCAocGFyZW50cyBmaXJzdCkgdG8gZW5zdXJlIHByb3BlciBoaWVyYXJjaHlcblx0Y29uc3Qgc29ydGVkVHlwZXMgPSBBcnJheS5mcm9tKHRvcG9sb2dpY2FUeXBlcy5lbnRyaWVzKCkpLnNvcnQoKGEsIGIpID0+IHtcblx0XHRjb25zdCBkZXB0aEEgPSAoYVsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRjb25zdCBkZXB0aEIgPSAoYlsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRyZXR1cm4gZGVwdGhBIC0gZGVwdGhCO1xuXHR9KTtcblx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBub2RlIF0gb2Ygc29ydGVkVHlwZXMpIHtcblx0XHRhbmFseXplci5hZGRUb3BvbG9naWNhVHlwZSh0eXBlUGF0aCwgbm9kZSk7XG5cdH1cblxuXHQvLyBGaXJzdCBwYXNzOiBjb2xsZWN0IGFsbCBkZWZpbml0aW9ucy5cblx0Ly8gTW9kdWxlLXNjb3BlIHRyYWNraW5nIChpbXBvcnRzL2V4cG9ydHMgZm9yIG1vZHVsZXMuanNvbikgaGFwcGVucyBpbiB0aGVcblx0Ly8gc2FtZSBwYXNzIOKAlCBpdCBuZWVkcyBvbmx5IHRoZSBBU1QsIG5vdCB0aGUgY29sbGVjdGVkIGRlZmluaXRpb25zLlxuXHRjb25zdCBtb2R1bGVHcmFwaEJ1aWxkZXIgPSBuZXcgTW9kdWxlR3JhcGhCdWlsZGVyKHByb2dyYW0pO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgQW5hbHl6aW5nIChkZWZpbml0aW9ucyk6ICR7c291cmNlRmlsZS5maWxlTmFtZX1gKTtcblx0XHR9XG5cblx0XHR0cnkge1xuXHRcdFx0YW5hbHl6ZXIuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0XHRtb2R1bGVHcmFwaEJ1aWxkZXIuYWRkRmlsZShzb3VyY2VGaWxlKTtcblx0XHR9IGNhdGNoIChlcnIpIHtcblx0XHRcdGNvbnNvbGUuZXJyb3IoYEVycm9yIGFuYWx5emluZyAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OmAsIGVycik7XG5cdFx0XHR0aHJvdyBlcnI7XG5cdFx0fVxuXHR9XG5cblx0Ly8gU2Vjb25kIHBhc3M6IGNvbGxlY3QgdXNhZ2VzIChub3cgYWxsIGRlZmluaXRpb25zIGFyZSBrbm93biwgaW5jbHVkaW5nIHRvcG9sb2dpY2EpXG5cdGFuYWx5emVyLnJlc2V0VXNhZ2VzKCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBBbmFseXppbmcgKHVzYWdlcyk6ICR7c291cmNlRmlsZS5maWxlTmFtZX1gKTtcblx0XHR9XG5cblx0XHR0cnkge1xuXHRcdFx0YW5hbHl6ZXIuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0XHRjb25zb2xlLmVycm9yKGBFcnJvciBhbmFseXppbmcgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfTpgLCBlcnIpO1xuXHRcdFx0dGhyb3cgZXJyO1xuXHRcdH1cblx0fVxuXG5cdC8vIEdlbmVyYXRlIHR5cGVzIGZyb20gbW5lbW9uaWNhIGFuYWx5c2lzXG5cdC8vIE5vdGU6IHRvcG9sb2dpY2EgdHlwZXMgYXJlIGFscmVhZHkgYWRkZWQgdG8gdGhlIGFuYWx5emVyJ3MgZ3JhcGggdmlhIGFkZFRvcG9sb2dpY2FUeXBlKClcblx0Y29uc3QgZ3JhcGggPSBhbmFseXplci5nZXRHcmFwaCgpO1xuXG5cdC8vIFBhdGgtYXdhcmUgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb24gKGlkZW50aXR5IGxhdyk6IHRoZSBnZW5lcmF0b3Jcblx0Ly8gcmVzb2x2ZXMgbmFtZXMgdGhyb3VnaCB0aGUgc2FtZSByZWxhdGl2ZS1maXJzdC9yb290L3VuaXF1ZSB0aWVycyB0aGVcblx0Ly8gYW5hbHl6ZXIgdXNlczsgdGhlIGFuYWx5emVyJ3Mgb3duIHZhbHVlL2ltcG9ydCB0aWVycyBhbHJlYWR5IHZldHRlZCB0aGVcblx0Ly8gdHlwZSBzdHJpbmdzIGR1cmluZyBleHRyYWN0aW9uXG5cdGNvbnN0IHJlZmVyZW5jZVJlc29sdmVyOiBHcmFwaFJlZmVyZW5jZVJlc29sdmVyID0gKHNpbXBsZU5hbWUsIGFuY2hvcikgPT4ge1xuXHRcdGNvbnN0IHJlZlJlc3VsdCA9IHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UoZ3JhcGgsIHNpbXBsZU5hbWUsIGFuY2hvcik7XG5cdFx0aWYgKHJlZlJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRyZXR1cm4gcmVmUmVzdWx0Lm5vZGU7XG5cdFx0fVxuXHRcdGlmIChyZWZSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0cmV0dXJuICdhbWJpZ3VvdXMnO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9O1xuXHRjb25zdCBnZW5lcmF0b3IgPSBuZXcgVHlwZXNHZW5lcmF0b3IoZ3JhcGgsIG9wdGlvbnMuZXNtLCBvcHRpb25zLm91dHB1dERpciwgcmVmZXJlbmNlUmVzb2x2ZXIpO1xuXG5cdC8vIENoZWNrIGlmIG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZSBpcyByZXF1ZXN0ZWQgKGxlZ2FjeSlcblx0Y29uc3QgdXNlTW9kdWxlQXVnbWVudGF0aW9uID0gb3B0aW9ucy5nbG9iYWxBdWdtZW50YXRpb24gPT09IGZhbHNlO1xuXG5cdC8vIEdlbmVyYXRlIGV2ZXJ5dGhpbmcgaW50byBtZW1vcnkgRklSU1Qg4oCUIHRoZSBoYXJkLWZhaWwgbGF3IGJlbG93IG1heVxuXHQvLyBhYm9ydCB0aGUgcnVuLCBhbmQgbm8gLnRhY3RpY2Egb3V0cHV0IGF0IGFsbCBtYXkgYmUgd3JpdHRlbiB0aGVuXG5cdGxldCBnZW5lcmF0ZWRUeXBlczogeyBjb250ZW50OiBzdHJpbmc7IHR5cGVzOiBzdHJpbmdbXSB9O1xuXHRsZXQgcmVnaXN0cnlUeXBlczogeyBjb250ZW50OiBzdHJpbmc7IHR5cGVzOiBzdHJpbmdbXSB9IHwgdW5kZWZpbmVkO1xuXHRsZXQgb3V0cHV0UGF0aDogc3RyaW5nO1xuXG5cdGlmICh1c2VNb2R1bGVBdWdtZW50YXRpb24pIHtcblx0XHQvLyBMZWdhY3kgbW9kZTogZ2VuZXJhdGUgZ2xvYmFsIGF1Z21lbnRhdGlvbiBmaWxlIChpbmRleC5kLnRzKVxuXHRcdGdlbmVyYXRlZFR5cGVzID0gZ2VuZXJhdG9yLmdlbmVyYXRlR2xvYmFsQXVnbWVudGF0aW9uKCk7XG5cdH0gZWxzZSB7XG5cdFx0Ly8gRGVmYXVsdCBtb2RlOiBnZW5lcmF0ZSB0eXBlcy50cyBmb3IgbWFudWFsIGltcG9ydHNcblx0XHRnZW5lcmF0ZWRUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZVR5cGVzRmlsZSgpO1xuXG5cdFx0Ly8gR2VuZXJhdGUgcmVnaXN0cnkudHMgZm9yIHR5cGUtc2FmZSBsb29rdXAoKSBmdW5jdGlvblxuXHRcdHJlZ2lzdHJ5VHlwZXMgPSBnZW5lcmF0b3IuZ2VuZXJhdGVUeXBlUmVnaXN0cnkoKTtcblx0fVxuXG5cdC8vIEhBUkQgRkFJTCAoZ3JhcGggaWRlbnRpdHkgbGF3KTogc2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIG1uZW1vbmljYVxuXHQvLyBkZWZpbml0aW9ucywgcGx1cyBncmFwaCByZWZlcmVuY2VzIHRoYXQgc3RheSBhbWJpZ3VvdXMgYWZ0ZXJcblx0Ly8gcGF0aC1hd2FyZSByZXNvbHV0aW9uIG9yIHJlc29sdmUgdG8gbm90aGluZy4gUHJpbnQgZXZlcnkgZmFpbHVyZSB3aXRoXG5cdC8vIGFsbCBpdHMgbG9jYXRpb25zIGFuZCB3cml0ZSBOTyAudGFjdGljYSBvdXRwdXQgYXQgYWxsLlxuXHRjb25zdCBmYXRhbEVycm9ycyA9IFsgLi4uYW5hbHl6ZXIuZ2V0UmVzb2x1dGlvbkVycm9ycygpLCAuLi5nZW5lcmF0b3IuZ2V0UmVzb2x1dGlvbkVycm9ycygpIF07XG5cdGlmIChmYXRhbEVycm9ycy5sZW5ndGggPiAwKSB7XG5cdFx0Y29uc3Qgc2VlbiA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdGxldCBwcmludGVkID0gMDtcblx0XHRmb3IgKGNvbnN0IGVycm9yIG9mIGZhdGFsRXJyb3JzKSB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtlcnJvci5tZXNzYWdlfXwke2Vycm9yLmxvY2F0aW9ucy5qb2luKCd8Jyl9YDtcblx0XHRcdGlmIChzZWVuLmhhcyhrZXkpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0c2Vlbi5hZGQoa2V5KTtcblx0XHRcdHByaW50ZWQrKztcblx0XHRcdGNvbnNvbGUuZXJyb3IoYHRhY3RpY2E6ICR7ZXJyb3IubWVzc2FnZX1gKTtcblx0XHRcdGZvciAoY29uc3QgbG9jYXRpb24gb2YgZXJyb3IubG9jYXRpb25zKSB7XG5cdFx0XHRcdGNvbnNvbGUuZXJyb3IoYCAgYXQgJHtsb2NhdGlvbn1gKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc29sZS5lcnJvcihgdGFjdGljYTogYWJvcnRpbmcg4oCUICR7cHJpbnRlZH0gcmVzb2x1dGlvbiBmYWlsdXJlKHMpOyBubyAudGFjdGljYSBvdXRwdXQgd3JpdHRlbmApO1xuXHRcdHJldHVybiAxO1xuXHR9XG5cblx0Ly8gUHJvamVjdCByb290IGFuY2hvcnMgdGhlIHJlbGF0aXZlIHBhdGhzIHRoZSB3cml0ZXIgZW1pdHM6IC50YWN0aWNhXG5cdC8vIG91dHB1dCBtdXN0IHN0YXkgcG9ydGFibGUgd2hlbiB0aGUgY2hlY2tvdXQgbW92ZXMgYmV0d2VlbiBtYWNoaW5lcy5cblx0Ly8gcmVzb2x2ZSgpIGJvdGggc2lkZXMg4oCUIHRzY29uZmlnUGF0aCBpdHNlbGYgbWF5IGJlIHJlbGF0aXZlLlxuXHRjb25zdCBwcm9qZWN0Um9vdCA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKSk7XG5cdGNvbnN0IHdyaXRlciA9IG5ldyBUeXBlc1dyaXRlcihvcHRpb25zLm91dHB1dERpciwgcHJvamVjdFJvb3QpO1xuXG5cdGlmICh1c2VNb2R1bGVBdWdtZW50YXRpb24pIHtcblx0XHQvLyBMZWdhY3kgbW9kZTogd3JpdGUgZ2xvYmFsIGF1Z21lbnRhdGlvbiBmaWxlIChpbmRleC5kLnRzKVxuXHRcdG91dHB1dFBhdGggPSB3cml0ZXIud3JpdGVHbG9iYWxBdWdtZW50YXRpb24oZ2VuZXJhdGVkVHlwZXMpO1xuXHR9IGVsc2Uge1xuXHRcdC8vIERlZmF1bHQgbW9kZTogd3JpdGUgdHlwZXMudHMgZm9yIG1hbnVhbCBpbXBvcnRzXG5cdFx0b3V0cHV0UGF0aCA9IHdyaXRlci53cml0ZVR5cGVzRmlsZShnZW5lcmF0ZWRUeXBlcyk7XG5cblx0XHRjb25zdCByZWdpc3RyeVBhdGggPSB3cml0ZXIud3JpdGVUbygncmVnaXN0cnkudHMnLCByZWdpc3RyeVR5cGVzIS5jb250ZW50KTtcblxuXHRcdC8vIEdlbmVyYXRlIGluZGV4LnRzIHRvIGV4cG9ydCBldmVyeXRoaW5nXG5cdFx0Y29uc3QgaW5kZXhDb250ZW50ID0gYC8vIEdlbmVyYXRlZCBieSBAbW5lbW9uaWNhL3RhY3RpY2EgLSBETyBOT1QgRURJVFxuLy8gRXhwb3J0IGFsbCBnZW5lcmF0ZWQgdHlwZXNcblxuZXhwb3J0ICogZnJvbSAnLi90eXBlcyR7b3B0aW9ucy5lc20gPyAnLmpzJyA6ICcnfSc7XG5leHBvcnQgKiBmcm9tICcuL3JlZ2lzdHJ5JHtvcHRpb25zLmVzbSA/ICcuanMnIDogJyd9JztcbmA7XG5cdFx0d3JpdGVyLndyaXRlVG8oJ2luZGV4LnRzJywgaW5kZXhDb250ZW50KTtcblxuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgcmVnaXN0cnkudHMgYXQ6ICR7cmVnaXN0cnlQYXRofWApO1xuXHRcdH1cblx0fVxuXG5cdC8vIEdlbmVyYXRlIGRlZmluaXRpb25zLmpzb24gYW5kIHVzYWdlcy5qc29uIGZvciBjb2RlIG5hdmlnYXRpb25cblx0Ly8gSW5jbHVkZSBib3RoIG1uZW1vbmljYSBhbmQgdG9wb2xvZ2ljYSBkZWZpbml0aW9uc1xuXHRjb25zdCBkZWZpbml0aW9ucyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0RGVmaW5pdGlvbnMoKSk7XG5cdGNvbnN0IHVzYWdlcyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0VXNhZ2VzKCkpO1xuXHRcblx0Ly8gQWRkIHRvcG9sb2dpY2EgdHlwZXMgdG8gZGVmaW5pdGlvbnNcblx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCB0eXBlTm9kZSBdIG9mIHRvcG9sb2dpY2FUeXBlcykge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHMgKHByZWZlciBtbmVtb25pY2EncyBhbmFseXNpcylcblx0XHRpZiAoZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXHRcdFxuXHRcdGNvbnN0IGRlZmluaXRpb246IGltcG9ydCgnLi90eXBlcycpLkRlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTm9kZS5uYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHt0eXBlTm9kZS5zb3VyY2VGaWxlfToke3R5cGVOb2RlLmxpbmV9OiR7dHlwZU5vZGUuY29sdW1ufWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiB0eXBlTm9kZS5wYXJlbnQgPyB0eXBlTm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0ZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0fVxuXG5cdC8vIExvY2FsLXNjb3BlIHdhbGsgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgUGhhc2UgMik6IGZ1bmN0aW9uL21ldGhvZC9hcnJvd1xuXHQvLyBzY29wZXMgb25seSAobm8gYmxvY2sgc2NvcGVzIOKAlCBkZWNpc2lvbiA1KSwgdmFyaWFibGVzIHdpdGggaXNNdXRhYmxlIGFuZFxuXHQvLyByZWFzc2lnbm1lbnQgc2l0ZXMgKGRlY2lzaW9uIDYpLiBSdW5zIGFmdGVyIGRlZmluaXRpb25zIGFyZSBrbm93biBzb1xuXHQvLyB2YXJpYWJsZSB0eXBlUGF0aHMgY2FuIHJlc29sdmU7IGhvbGRlclNjb3BlSWQgaXMgYXR0YWNoZWQgdG8gdXNhZ2VzXG5cdC8vIGJlZm9yZSB0aGV5IGFyZSB3cml0dGVuLlxuXHRjb25zdCBzY29wZVdhbGtlciA9IG5ldyBMb2NhbFNjb3BlV2Fsa2VyKCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdHNjb3BlV2Fsa2VyLmFkZEZpbGUoc291cmNlRmlsZSk7XG5cdH1cblx0Y29uc3Qgc2NvcGVSZXNvbHZlcjogU2NvcGVUeXBlUmVzb2x2ZXIgPSB7XG5cdFx0cmVzb2x2ZUJ5TmFtZSA6IChuYW1lOiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQgPT4ge1xuXHRcdFx0aWYgKGRlZmluaXRpb25zLmhhcyhuYW1lKSkge1xuXHRcdFx0XHRyZXR1cm4gbmFtZTtcblx0XHRcdH1cblx0XHRcdGxldCBmb3VuZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdFx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCBkZWZpbml0aW9uIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRcdFx0aWYgKGRlZmluaXRpb24ubmFtZSAhPT0gbmFtZSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdC8vIEFtYmlndW91cyBuYW1lIOKAlCBubyB0eXBlIGNoZWNrZXIsIHNvIHJlZnVzZSB0byBndWVzc1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Zm91bmQgPSBmdWxsUGF0aDtcblx0XHRcdH1cblx0XHRcdHJldHVybiBmb3VuZDtcblx0XHR9LFxuXHRcdGhhc1BhdGggOiAoZnVsbFBhdGg6IHN0cmluZyk6IGJvb2xlYW4gPT4ge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fSxcblx0XHQvLyBUaGUgYW5hbHl6ZXIncyBvd24gbG9va3VwIGxhdywgYWdhaW5zdCB0aGUgc2FtZSBjb21wbGV0ZSBncmFwaCB0aGVcblx0XHQvLyB1c2FnZXMgcGFzcyByZXNvbHZlZCB3aXRoIOKAlCBhIGxvb2t1cCgpIGluaXRpYWxpemVyIHRoZSBhbmFseXplclxuXHRcdC8vIGFjY2VwdGVkIChlLmcuIGFuIGltcG9ydGVkIEhvbGRlci5sb29rdXAoJ1Rva2VuJykpIGxhbmRzIHRoZSBzYW1lXG5cdFx0Ly8gZnVsbFBhdGggaW4gc2NvcGVzLmpzb24gaW5zdGVhZCBvZiBzdGFydmluZyB0aGUgY3JlYXRpb24tZ3JhcGhcblx0XHQvLyBhbmNob3JzLiBSZWplY3RlZCBsb29rdXBzIHN0YXkgdHlwZVBhdGgtbGVzcyBoZXJlOyB0aGUgYW5hbHl6ZXJcblx0XHQvLyBhbHJlYWR5IGhhcmQtZmFpbGVkIHRoZSBydW4gYWJvdmUuXG5cdFx0cmVzb2x2ZUxvb2t1cCA6IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCA9PiB7XG5cdFx0XHRjb25zdCByZXNvbHZlZCA9IGFuYWx5emVyLnJlc29sdmVMb29rdXBDYWxsUGF0aChjYWxsKTtcblx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHR9LFxuXHR9O1xuXHRjb25zdCBzY29wZUFuYWx5c2lzID0gc2NvcGVXYWxrZXIuYnVpbGQoc2NvcGVSZXNvbHZlcik7XG5cdExvY2FsU2NvcGVXYWxrZXIuYXR0YWNoSG9sZGVyU2NvcGVJZHModXNhZ2VzLCBzY29wZVdhbGtlcik7XG5cblx0Y29uc3QgZGVmaW5pdGlvbnNQYXRoID0gd3JpdGVyLndyaXRlRGVmaW5pdGlvbnNGaWxlKGRlZmluaXRpb25zKTtcblx0Y29uc3QgdXNhZ2VzUGF0aCA9IHdyaXRlci53cml0ZVVzYWdlc0ZpbGUodXNhZ2VzKTtcblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBkZWZpbml0aW9ucy5qc29uIGF0OiAke2RlZmluaXRpb25zUGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHVzYWdlcy5qc29uIGF0OiAke3VzYWdlc1BhdGh9YCk7XG5cdH1cblxuXHQvLyBEZXRlcm1pbmUgRURTIHNldHRpbmc6IGV4cGxpY2l0IGZsYWcgPiBhdXRvLWRldGVjdCBkaXZlID4gZGVmYXVsdCBvZmZcblx0bGV0IGVuYWJsZUVEUyA9IG9wdGlvbnMuZWRzO1xuXHRpZiAoZW5hYmxlRURTID09PSB1bmRlZmluZWQpIHtcblx0XHRlbmFibGVFRFMgPSBoYXNEaXZlRGVwZW5kZW5jeShwcm9qZWN0RGlyKTtcblx0fVxuXG5cdGlmIChlbmFibGVFRFMpIHtcblx0XHRjb25zdCBlZHMgPSBhbmFseXplci5nZXRFRFNVc2FnZXMoKTtcblx0XHRhdHRhY2hXcmFwSm9pbkRhdGEoZWRzLCBzY29wZVdhbGtlciwgc2NvcGVBbmFseXNpcyk7XG5cdFx0Y29uc3QgZWRzUGF0aCA9IHdyaXRlci53cml0ZUVEU0ZpbGUoZWRzKTtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGVkcy5qc29uIGF0OiAke2Vkc1BhdGh9YCk7XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIGZsb3cuanNvbiAobmF0aXZlIGluc3RhbmNlIHVzYWdlIHRyYWNraW5nKVxuXHRjb25zdCBmbG93ID0gYW5hbHl6ZXIuZ2V0Rmxvd1VzYWdlcygpO1xuXHRjb25zdCBmbG93UGF0aCA9IHdyaXRlci53cml0ZUZsb3dGaWxlKGZsb3cpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3QgZmxvd0NvdW50ID0gQXJyYXkuZnJvbShmbG93LnZhbHVlcygpKS5yZWR1Y2UoKHN1bSwgYXJyKSA9PiBzdW0gKyBhcnIubGVuZ3RoLCAwKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGZsb3cuanNvbiBhdDogJHtmbG93UGF0aH0gKCR7Zmxvd0NvdW50fSBmbG93IGVudHJpZXMpYCk7XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgbW9kdWxlcy5qc29uIChtb2R1bGUtc2NvcGUgZ3JhcGg6IGltcG9ydHMvZXhwb3J0cyxcblx0Ly8gZGVwZW5kZW5jaWVzLCBjeWNsZXMsIGNyb3NzLW1vZHVsZSBtbmVtb25pY2EtdHlwZSBlZGdlcylcblx0Y29uc3QgZGVmaW5lZFR5cGVzQnlGaWxlID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZ1tdPigpO1xuXHRmb3IgKGNvbnN0IFsgZnVsbFBhdGgsIGRlZmluaXRpb24gXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdGNvbnN0IHsgbG9jYXRpb24gfSA9IGRlZmluaXRpb247XG5cdFx0Y29uc3QgbGFzdENvbG9uID0gbG9jYXRpb24ubGFzdEluZGV4T2YoJzonKTtcblx0XHRjb25zdCBwcmV2Q29sb24gPSBsb2NhdGlvbi5sYXN0SW5kZXhPZignOicsIGxhc3RDb2xvbiAtIDEpO1xuXHRcdGNvbnN0IGZpbGUgPSBsb2NhdGlvbi5zbGljZSgwLCBwcmV2Q29sb24pO1xuXHRcdGNvbnN0IGxpc3QgPSBkZWZpbmVkVHlwZXNCeUZpbGUuZ2V0KGZpbGUpID8/IFtdO1xuXHRcdGxpc3QucHVzaChmdWxsUGF0aCk7XG5cdFx0ZGVmaW5lZFR5cGVzQnlGaWxlLnNldChmaWxlLCBsaXN0KTtcblx0fVxuXHRjb25zdCBtb2R1bGVHcmFwaCA9IG1vZHVsZUdyYXBoQnVpbGRlci5idWlsZChkZWZpbmVkVHlwZXNCeUZpbGUpO1xuXHRjb25zdCBtb2R1bGVzUGF0aCA9IHdyaXRlci53cml0ZU1vZHVsZXNGaWxlKG1vZHVsZUdyYXBoKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IG1vZHVsZUNvdW50ID0gbW9kdWxlR3JhcGgubW9kdWxlcy5zaXplO1xuXHRcdGNvbnN0IGVkZ2VDb3VudCA9IG1vZHVsZUdyYXBoLmVkZ2VzLmxlbmd0aDtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIG1vZHVsZXMuanNvbiBhdDogJHttb2R1bGVzUGF0aH0gKCR7bW9kdWxlQ291bnR9IG1vZHVsZXMsICR7ZWRnZUNvdW50fSBlZGdlcylgKTtcblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBzY29wZXMuanNvbiAobG9jYWwtc2NvcGUgd2Fsa2VyOiBzY29wZXMsIHZhcmlhYmxlcyxcblx0Ly8gcmVhc3NpZ25tZW50IGZsb3ctdGVybWluYXRpb24gcG9pbnRzKVxuXHRjb25zdCBzY29wZXNQYXRoID0gd3JpdGVyLndyaXRlU2NvcGVzRmlsZShzY29wZUFuYWx5c2lzKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IHNjb3BlQ291bnQgPSBzY29wZUFuYWx5c2lzLnNjb3Blcy5zaXplO1xuXHRcdGNvbnN0IHZhcmlhYmxlQ291bnQgPSBzY29wZUFuYWx5c2lzLnZhcmlhYmxlcy5zaXplO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgc2NvcGVzLmpzb24gYXQ6ICR7c2NvcGVzUGF0aH0gKCR7c2NvcGVDb3VudH0gc2NvcGVzLCAke3ZhcmlhYmxlQ291bnR9IHZhcmlhYmxlcylgKTtcblx0fVxuXG5cdC8vIFRoZSBpbnNpZGUtb3V0IGNyZWF0aW9uIHdhbGsgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgUGhhc2UgMyk6IGFuY2hvcnNcblx0Ly8gYXJlIHRoZSBpbnN0YW50aWF0aW9uIHVzYWdlczsgY2FsbGVycyBhcmUgZm9sbG93ZWQgc2FtZS1maWxlIGFuZFxuXHQvLyBjcm9zcy1maWxlIChtb2R1bGUgZ3JhcGgsIGJhcnJlbHMgY2hhc2VkKSB1bnRpbCBvbmx5IHN0YXJ0ZXJzIHJlbWFpbi5cblx0Y29uc3Qgc291cmNlRmlsZXNCeVBhdGggPSBuZXcgTWFwPHN0cmluZywgdHMuU291cmNlRmlsZT4oKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0c291cmNlRmlsZXNCeVBhdGguc2V0KHBhdGgucmVzb2x2ZShzb3VyY2VGaWxlLmZpbGVOYW1lKSwgc291cmNlRmlsZSk7XG5cdH1cblx0Y29uc3QgY3JlYXRpb25HcmFwaEJ1aWxkZXIgPSBuZXcgQ3JlYXRpb25HcmFwaEJ1aWxkZXIobW9kdWxlR3JhcGgsIHNjb3BlQW5hbHlzaXMsIHNjb3BlV2Fsa2VyLCBzb3VyY2VGaWxlc0J5UGF0aCk7XG5cdGNvbnN0IGNyZWF0aW9uR3JhcGggPSBjcmVhdGlvbkdyYXBoQnVpbGRlci5idWlsZCh1c2FnZXMpO1xuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBpbnN0cnVtZW50YXRpb24uanNvbiAoZnJhbWV3b3JrIGxpZmVjeWNsZSBjcm9zc3JvYWRzXG5cdC8vIGZyb20gdGhlIGxvYWRlZCBwbHVnaW5zIOKAlCBzeW50YWN0aWMgZGV0ZWN0aW9uIG5lZWRzIG5vIGRpdmVcblx0Ly8gZGVwZW5kZW5jeSwgdW5saWtlIGVkcy5qc29uKS4gdjIgY2FycmllcyB0aGUgY3JlYXRpb24gZ3JhcGhcblx0Ly8gYWxvbmdzaWRlIHRoZSBwb2ludHMuXG5cdGNvbnN0IGluc3RydW1lbnRhdGlvbiA9IGFuYWx5emVyLmdldEluc3RydW1lbnRhdGlvblBvaW50cygpO1xuXHRjb25zdCBpbnN0cnVtZW50YXRpb25QYXRoID0gd3JpdGVyLndyaXRlSW5zdHJ1bWVudGF0aW9uRmlsZShpbnN0cnVtZW50YXRpb24sIGNyZWF0aW9uR3JhcGgpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3Qgbm9kZUNvdW50ID0gY3JlYXRpb25HcmFwaC5ub2Rlcy5sZW5ndGg7XG5cdFx0Y29uc3QgZWRnZUNvdW50ID0gY3JlYXRpb25HcmFwaC5lZGdlcy5sZW5ndGg7XG5cdFx0Y29uc3QgYW5jaG9yQ291bnQgPSBjcmVhdGlvbkdyYXBoLmFuY2hvcnMubGVuZ3RoO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaW5zdHJ1bWVudGF0aW9uLmpzb24gYXQ6ICR7aW5zdHJ1bWVudGF0aW9uUGF0aH0gKCR7aW5zdHJ1bWVudGF0aW9uLmxlbmd0aH0gcG9pbnRzKWApO1xuXHRcdGNvbnNvbGUubG9nKGAgIGNyZWF0aW9uIGdyYXBoOiAke25vZGVDb3VudH0gbm9kZXMsICR7ZWRnZUNvdW50fSBlZGdlcywgJHthbmNob3JDb3VudH0gYW5jaG9yc2ApO1xuXHR9XG5cblx0Ly8gR2VuZXJhdGUgaGllcmFyY2h5Lmpzb24gKHN0cnVjdHVyZWQpIGFuZCBoaWVyYXJjaHkudHh0IChBU0NJSSB0cmVlKSBmb3IgdGhlIFRyaWVcblx0Y29uc3QgaGllcmFyY2h5Um9vdHMgPSBncmFwaC50b0hpZXJhcmNoeSgpO1xuXHRjb25zdCBoaWVyYXJjaHlKc29uUGF0aCA9IHdyaXRlci53cml0ZUhpZXJhcmNoeUZpbGUoaGllcmFyY2h5Um9vdHMpO1xuXHRjb25zdCBoaWVyYXJjaHlUZXh0ID0gcmVuZGVyVHlwZUhpZXJhcmNoeShncmFwaCk7XG5cdGNvbnN0IGhpZXJhcmNoeVR4dFBhdGggPSB3cml0ZXIud3JpdGVUbygnaGllcmFyY2h5LnR4dCcsIGhpZXJhcmNoeVRleHQpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBoaWVyYXJjaHkuanNvbiBhdDogJHtoaWVyYXJjaHlKc29uUGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGhpZXJhcmNoeS50eHQgYXQ6ICR7aGllcmFyY2h5VHh0UGF0aH1gKTtcblx0fVxuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHR5cGVzIGF0OiAke291dHB1dFBhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coYE1vZGU6ICR7dXNlTW9kdWxlQXVnbWVudGF0aW9uID8gJ2dsb2JhbCBhdWdtZW50YXRpb24gKGxlZ2FjeSknIDogJ3R5cGVzIGZpbGUgKGRlZmF1bHQpJ31gKTtcblx0XHRjb25zb2xlLmxvZyhgRm91bmQgJHtnZW5lcmF0ZWRUeXBlcy50eXBlcy5sZW5ndGh9IHR5cGVzOmApO1xuXHRcdHByaW50VHlwZUhpZXJhcmNoeShncmFwaCk7XG5cdH0gZWxzZSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCAke2dlbmVyYXRlZFR5cGVzLnR5cGVzLmxlbmd0aH0gdHlwZXMgYXQgJHtvcHRpb25zLm91dHB1dERpciB8fCAnLnRhY3RpY2EnfWApO1xuXHRcdGlmICh1c2VNb2R1bGVBdWdtZW50YXRpb24pIHtcblx0XHRcdGNvbnNvbGUubG9nKCdVc2luZyBnbG9iYWwgYXVnbWVudGF0aW9uIG1vZGUgKGxlZ2FjeSwgdXNlIGRlZmF1bHQgbW9kZSBmb3IgdHlwZXMudHMgb25seSknKTtcblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gMDtcbn1cblxuLyoqXG4gKiBXYXRjaCBtb2RlXG4gKi9cbmZ1bmN0aW9uIHdhdGNoIChvcHRpb25zOiBDTElPcHRpb25zKTogdm9pZCB7XG5cdGNvbnNvbGUubG9nKCdTdGFydGluZyB3YXRjaCBtb2RlLi4uJyk7XG5cblx0Ly8gSW5pdGlhbCBydW5cblx0cnVuKG9wdGlvbnMpO1xuXG5cdC8vIFNldCB1cCBmaWxlIHdhdGNoaW5nXG5cdGNvbnN0IGNob2tpZGFyID0gcmVxdWlyZSgnY2hva2lkYXInKTtcblx0Y29uc3QgdHNjb25maWdQYXRoID0gZmluZFRzQ29uZmlnKG9wdGlvbnMucHJvamVjdCk7XG5cblx0aWYgKCF0c2NvbmZpZ1BhdGgpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjogQ291bGQgbm90IGZpbmQgdHNjb25maWcuanNvbicpO1xuXHRcdHByb2Nlc3MuZXhpdCgxKTtcblx0fVxuXG5cdGNvbnN0IHByb2plY3REaXIgPSBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKTtcblx0Y29uc3Qgd2F0Y2hQYXRocyA9IG9wdGlvbnMuaW5jbHVkZSB8fCBbICcqKi8qLnRzJyBdO1xuXHRjb25zdCBpZ25vcmVQYXRocyA9IG9wdGlvbnMuZXhjbHVkZSB8fCBbICcqKi8qLmQudHMnLCAnbm9kZV9tb2R1bGVzLyoqJywgJy50YWN0aWNhLyoqJyBdO1xuXG5cdGNvbnN0IHdhdGNoZXIgPSBjaG9raWRhci53YXRjaCh3YXRjaFBhdGhzLCB7XG5cdFx0Y3dkICAgICAgICA6IHByb2plY3REaXIsXG5cdFx0aWdub3JlZCAgICA6IGlnbm9yZVBhdGhzLFxuXHRcdHBlcnNpc3RlbnQgOiB0cnVlLFxuXHR9KTtcblxuXHR3YXRjaGVyLm9uKCdjaGFuZ2UnLCAoZmlsZVBhdGg6IHN0cmluZykgPT4ge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBGaWxlIGNoYW5nZWQ6ICR7ZmlsZVBhdGh9YCk7XG5cdFx0fVxuXHRcdHJ1bihvcHRpb25zKTtcblx0fSk7XG5cblx0d2F0Y2hlci5vbignYWRkJywgKGZpbGVQYXRoOiBzdHJpbmcpID0+IHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgRmlsZSBhZGRlZDogJHtmaWxlUGF0aH1gKTtcblx0XHR9XG5cdFx0cnVuKG9wdGlvbnMpO1xuXHR9KTtcblxuXHRjb25zb2xlLmxvZygnV2F0Y2hpbmcgZm9yIGNoYW5nZXMuLi4gKFByZXNzIEN0cmwrQyB0byBzdG9wKScpO1xufVxuXG4vKipcbiAqIE1haW4gZW50cnkgcG9pbnRcbiAqL1xuZnVuY3Rpb24gbWFpbiAoKTogdm9pZCB7XG5cdGNvbnN0IGFyZ3MgPSBwcm9jZXNzLmFyZ3Yuc2xpY2UoMik7XG5cdGNvbnN0IG9wdGlvbnMgPSBwYXJzZUFyZ3MoYXJncyk7XG5cblx0aWYgKG9wdGlvbnMuaGVscCkge1xuXHRcdHByaW50SGVscCgpO1xuXHRcdHByb2Nlc3MuZXhpdCgwKTtcblx0fVxuXG5cdHRyeSB7XG5cdFx0aWYgKG9wdGlvbnMud2F0Y2gpIHtcblx0XHRcdHdhdGNoKG9wdGlvbnMpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHRjb25zdCBjb2RlID0gcnVuKG9wdGlvbnMpO1xuXHRcdFx0aWYgKGNvZGUpIHtcblx0XHRcdFx0cHJvY2Vzcy5leGl0KGNvZGUpO1xuXHRcdFx0fVxuXHRcdH1cblx0fSBjYXRjaCAoZXJyb3IpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjonLCBlcnJvciBpbnN0YW5jZW9mIEVycm9yID8gZXJyb3IubWVzc2FnZSA6IGVycm9yKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cbn1cblxuLy8gUnVuIGlmIGV4ZWN1dGVkIGRpcmVjdGx5XG5pZiAocmVxdWlyZS5tYWluID09PSBtb2R1bGUpIHtcblx0bWFpbigpO1xufVxuXG5leHBvcnQge1xuXHRtYWluLCBydW4sIHdhdGNoLCBwYXJzZUFyZ3MgXG59O1xuIl19