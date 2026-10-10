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
 * Display-only: siblings are sorted by fullPath at render time (code-unit
 * order — default-collection PascalCase roots land before the
 * `collection_N::`-prefixed ones). The graph itself keeps discovery order;
 * hierarchy.json is unaffected.
 */
function renderTypeHierarchy(graph) {
    const lines = ['Type Hierarchy (Trie):'];
    function sortedByFullPath(nodes) {
        const sorted = Array.from(nodes);
        sorted.sort((a, b) => {
            if (a.fullPath < b.fullPath) {
                return -1;
            }
            if (a.fullPath > b.fullPath) {
                return 1;
            }
            return 0;
        });
        return sorted;
    }
    function renderNode(node, prefix = '', isLast = true) {
        const connector = isLast ? '└── ' : '├── ';
        // Use node.fullPath directly and convert dots to underscores
        const instanceName = node.fullPath.replace(/\./g, '_');
        lines.push(`${prefix}${connector}${instanceName}`);
        const children = sortedByFullPath(Array.from(node.children.values()));
        const newPrefix = prefix + (isLast ? '    ' : '│   ');
        for (let i = 0; i < children.length; i++) {
            renderNode(children[i], newPrefix, i === children.length - 1);
        }
    }
    const roots = sortedByFullPath(Array.from(graph.roots.values()));
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
    const definitionsPath = writer.writeDefinitionsFile(definitions, graph);
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
    // Always generate control.json (lethe contract, format 1.1): the same
    // creation graph and points as instrumentation.json, rendered under the
    // cross-language `callers`/`points` keys.
    const controlPath = writer.writeControlFile(instrumentation, creationGraph);
    if (options.verbose) {
        console.log(`Generated control.json at: ${controlPath}`);
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
    // Always generate collections.json (the collection manifest: ids, display
    // names, Option-B registry interfaces, call sites — the id↔interface join
    // key between the prefixed graph outputs and the types.ts aliases)
    const collectionsPath = writer.writeCollectionsFile(analyzer.getCollectionsManifest());
    if (options.verbose) {
        console.log(`Generated collections.json at: ${collectionsPath}`);
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQSs4Qlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUE3OEI1Qix1Q0FBeUI7QUFDekIsMkNBQTZCO0FBQzdCLG1DQUF1QztBQUN2QywrQ0FBaUM7QUFDakMseUNBQStDO0FBQy9DLCtEQUEyRDtBQUMzRCwyQ0FFcUI7QUFDckIscUNBQXVDO0FBQ3ZDLGlEQUFvRDtBQUNwRCxxREFBd0Q7QUFDeEQscUNBRWtCO0FBQ2xCLG1DQUVpQjtBQTBCakI7O0dBRUc7QUFDSCxTQUFTLFNBQVMsQ0FBRSxJQUFjO0lBQ2pDLE1BQU0sT0FBTyxHQUFlLEVBQUUsQ0FBQztJQUUvQixLQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRSxDQUFDO1FBQ3RDLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBRSxDQUFDLENBQUUsQ0FBQztRQUV0QixRQUFRLEdBQUcsRUFBRSxDQUFDO1lBQ2QsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFNBQVM7Z0JBQ2IsT0FBTyxDQUFDLEtBQUssR0FBRyxJQUFJLENBQUM7Z0JBQ3JCLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssV0FBVztnQkFDZixPQUFPLENBQUMsT0FBTyxHQUFHLElBQUksQ0FBRSxFQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUM5QixNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFVBQVU7Z0JBQ2QsT0FBTyxDQUFDLFNBQVMsR0FBRyxJQUFJLENBQUUsRUFBRSxDQUFDLENBQUUsQ0FBQztnQkFDaEMsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxXQUFX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QUM7WUFDcEIsQ0FBQztRQUNGLENBQUM7SUFDRixDQUFDO0lBQUMsT0FBTyxLQUFLLEVBQUUsQ0FBQztRQUNoQixPQUFPLENBQUMsS0FBSyxDQUFDLFFBQVEsRUFBRSxLQUFLLFlBQVksS0FBSyxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUMsT0FBTyxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQztRQUN4RSxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDO0lBQ2pCLENBQUM7QUFDRixDQUFDO0FBRUQsMkJBQTJCO0FBQzNCLElBQUksT0FBTyxDQUFDLElBQUksS0FBSyxNQUFNLEVBQUUsQ0FBQztJQUM3QixJQUFJLEVBQUUsQ0FBQztBQUNSLENBQUMiLCJzb3VyY2VzQ29udGVudCI6WyIjIS91c3IvYmluL2VudiBub2RlXG4ndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIGZzIGZyb20gJ2ZzJztcbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQgeyBjcmVhdGVSZXF1aXJlIH0gZnJvbSAnbW9kdWxlJztcbmltcG9ydCAqIGFzIHRzIGZyb20gJ3R5cGVzY3JpcHQnO1xuaW1wb3J0IHsgTW5lbW9uaWNhQW5hbHl6ZXIgfSBmcm9tICcuL2FuYWx5emVyJztcbmltcG9ydCB7IFRvcG9sb2dpY2FBbmFseXplciB9IGZyb20gJy4vdG9wb2xvZ2ljYS1hbmFseXplcic7XG5pbXBvcnQge1xuXHRUeXBlc0dlbmVyYXRvciwgR3JhcGhSZWZlcmVuY2VSZXNvbHZlciBcbn0gZnJvbSAnLi9nZW5lcmF0b3InO1xuaW1wb3J0IHsgVHlwZXNXcml0ZXIgfSBmcm9tICcuL3dyaXRlcic7XG5pbXBvcnQgeyBNb2R1bGVHcmFwaEJ1aWxkZXIgfSBmcm9tICcuL21vZHVsZS1ncmFwaCc7XG5pbXBvcnQgeyBDcmVhdGlvbkdyYXBoQnVpbGRlciB9IGZyb20gJy4vY3JlYXRpb24tZ3JhcGgnO1xuaW1wb3J0IHtcblx0TG9jYWxTY29wZVdhbGtlciwgU2NvcGVUeXBlUmVzb2x2ZXJcbn0gZnJvbSAnLi9zY29wZXMnO1xuaW1wb3J0IHtcblx0cmVzb2x2ZUdyYXBoVHlwZVJlZmVyZW5jZSwgVHlwZUdyYXBoSW1wbCBcbn0gZnJvbSAnLi9ncmFwaCc7XG5pbXBvcnQge1xuXHRUYWN0aWNhQ29uZmlnLCBUeXBlTm9kZSwgRURTSW5mbywgU2NvcGVBbmFseXNpc1xufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7IFRhY3RpY2FQbHVnaW4gfSBmcm9tICcuL3BsdWdpbnMnO1xuXG4vKipcbiAqIENMSSBlbnRyeSBwb2ludCBmb3IgVGFjdGljYVxuICpcbiAqIFJ1bnMgdGhlIGFuYWx5emVyIG92ZXIgYSB0c2NvbmZpZyBwcm9qZWN0IGFuZCB3cml0ZXMgLnRhY3RpY2EvIG91dHB1dFxuICovXG5cbmludGVyZmFjZSBDTElPcHRpb25zIGV4dGVuZHMgVGFjdGljYUNvbmZpZyB7XG5cdHdhdGNoPzogYm9vbGVhbjtcblx0cHJvamVjdD86IHN0cmluZztcblx0aGVscD86IGJvb2xlYW47XG5cdC8qKiBDdXN0b20gdG9wb2xvZ2ljYSBkaXJlY3RvcmllcyB0byBzY2FuICovXG5cdHRvcG9sb2dpY2FEaXJzPzogc3RyaW5nW107XG5cdC8qKiBBZGQgLmpzIGV4dGVuc2lvbnMgdG8gcmVsYXRpdmUgaW1wb3J0cyBmb3IgRVNNIE5vZGVOZXh0IHJlc29sdXRpb24gKi9cblx0ZXNtPzogYm9vbGVhbjtcblx0LyoqIEVuYWJsZSBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHRyYWNraW5nICovXG5cdGVkcz86IGJvb2xlYW47XG5cdC8qKiBQcm9ncmFtbWF0aWMgcGx1Z2luczsgY29uZmlnLWZpbGUgcGx1Z2lucyBhcmUgYXBwZW5kZWQgYWZ0ZXIgdGhlc2UgKi9cblx0cGx1Z2lucz86IFRhY3RpY2FQbHVnaW5bXTtcbn1cblxuLyoqXG4gKiBQYXJzZSBjb21tYW5kIGxpbmUgYXJndW1lbnRzXG4gKi9cbmZ1bmN0aW9uIHBhcnNlQXJncyAoYXJnczogc3RyaW5nW10pOiBDTElPcHRpb25zIHtcblx0Y29uc3Qgb3B0aW9uczogQ0xJT3B0aW9ucyA9IHt9O1xuXG5cdGZvciAobGV0IGkgPSAwOyBpIDwgYXJncy5sZW5ndGg7IGkrKykge1xuXHRcdGNvbnN0IGFyZyA9IGFyZ3NbIGkgXTtcblxuXHRcdHN3aXRjaCAoYXJnKSB7XG5cdFx0Y2FzZSAnLXcnOlxuXHRcdGNhc2UgJy0td2F0Y2gnOlxuXHRcdFx0b3B0aW9ucy53YXRjaCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctcCc6XG5cdFx0Y2FzZSAnLS1wcm9qZWN0Jzpcblx0XHRcdG9wdGlvbnMucHJvamVjdCA9IGFyZ3NbICsraSBdO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLW8nOlxuXHRcdGNhc2UgJy0tb3V0cHV0Jzpcblx0XHRcdG9wdGlvbnMub3V0cHV0RGlyID0gYXJnc1sgKytpIF07XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaSc6XG5cdFx0Y2FzZSAnLS1pbmNsdWRlJzpcblx0XHRcdG9wdGlvbnMuaW5jbHVkZSA9IChvcHRpb25zLmluY2x1ZGUgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1lJzpcblx0XHRjYXNlICctLWV4Y2x1ZGUnOlxuXHRcdFx0b3B0aW9ucy5leGNsdWRlID0gKG9wdGlvbnMuZXhjbHVkZSB8fCBbXSkuY29uY2F0KGFyZ3NbICsraSBdLnNwbGl0KCcsJykpO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLW0nOlxuXHRcdGNhc2UgJy0tbW9kdWxlLWF1Z21lbnRhdGlvbic6XG5cdFx0XHRvcHRpb25zLmdsb2JhbEF1Z21lbnRhdGlvbiA9IGZhbHNlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXYnOlxuXHRcdGNhc2UgJy0tdmVyYm9zZSc6XG5cdFx0XHRvcHRpb25zLnZlcmJvc2UgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXQnOlxuXHRcdGNhc2UgJy0tdG9wb2xvZ2ljYSc6XG5cdFx0XHRvcHRpb25zLnRvcG9sb2dpY2FEaXJzID0gKG9wdGlvbnMudG9wb2xvZ2ljYURpcnMgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZXNtJzpcblx0XHRcdG9wdGlvbnMuZXNtID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tbm8tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gZmFsc2U7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaCc6XG5cdFx0Y2FzZSAnLS1oZWxwJzpcblx0XHRcdG9wdGlvbnMuaGVscCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gb3B0aW9ucztcbn1cblxuLyoqXG4gKiBQcmludCBoZWxwIG1lc3NhZ2VcbiAqL1xuZnVuY3Rpb24gcHJpbnRIZWxwICgpOiB2b2lkIHtcblx0Y29uc29sZS5sb2coYFxuVGFjdGljYSAtIFR5cGUgZGVmaW5pdGlvbiBnZW5lcmF0b3IgZm9yIE1uZW1vbmljYVxuXG5Vc2FnZTogdGFjdGljYSBbb3B0aW9uc11cblxuT3B0aW9uczpcbiAgLXcsIC0td2F0Y2ggICAgICAgICAgICAgICBXYXRjaCBmb3IgZmlsZSBjaGFuZ2VzIGFuZCByZWdlbmVyYXRlIHR5cGVzXG4gIC1wLCAtLXByb2plY3QgICAgICAgICAgICAgUGF0aCB0byB0c2NvbmZpZy5qc29uIChkZWZhdWx0OiAuL3RzY29uZmlnLmpzb24pXG4gIC1vLCAtLW91dHB1dCAgICAgICAgICAgICAgT3V0cHV0IGRpcmVjdG9yeSBmb3IgZ2VuZXJhdGVkIHR5cGVzIChkZWZhdWx0OiAudGFjdGljYSlcbiAgLWksIC0taW5jbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGluY2x1ZGVcbiAgLWUsIC0tZXhjbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGV4Y2x1ZGVcbiAgLXQsIC0tdG9wb2xvZ2ljYSAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIHRvIHNjYW5cbiAgLW0sIC0tbW9kdWxlLWF1Z21lbnRhdGlvbiBVc2UgbW9kdWxlIGF1Z21lbnRhdGlvbiBpbnN0ZWFkIG9mIGdsb2JhbCAobGVnYWN5IG1vZGUpXG4gIC0tZXNtICAgICAgICAgICAgICAgICAgICAgQWRkIC5qcyBleHRlbnNpb25zIHRvIHJlbGF0aXZlIGltcG9ydHMgKE5vZGVOZXh0IEVTTSlcbiAgLS1lZHMgICAgICAgICAgICAgICAgICAgICBFbmFibGUgRURTIChFeGVjdXRpb24gRGF0YSBTdG9yYWdlKSB0cmFja2luZ1xuICAtLW5vLWVkcyAgICAgICAgICAgICAgICAgIERpc2FibGUgRURTIHRyYWNraW5nXG4gIC12LCAtLXZlcmJvc2UgICAgICAgICAgICAgRW5hYmxlIHZlcmJvc2UgbG9nZ2luZ1xuICAtaCwgLS1oZWxwICAgICAgICAgICAgICAgIFNob3cgdGhpcyBoZWxwIG1lc3NhZ2VcblxuQ29uZmlndXJhdGlvbjpcbiAgRnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiB2b2NhYnVsYXJ5IGlzIHN1cHBsaWVkIGJ5IHBsdWdpbnMuIFBsYWNlIGFcbiAgLnRhY3RpY2EuanMgKG9yIHRhY3RpY2EuY29uZmlnLmpzKSBuZXh0IHRvIHlvdXIgdHNjb25maWcuanNvbjpcblxuICAgICAgbW9kdWxlLmV4cG9ydHMgPSB7IHBsdWdpbnM6IFsgJ3lvdXItZnJhbWV3b3JrLWFkYXB0ZXIvdGFjdGljYScgXSB9O1xuXG4gIEVudHJpZXMgYXJlIG1vZHVsZSBzcGVjaWZpZXJzIChyZXF1aXJlZCByZWxhdGl2ZSB0byB0aGUgY29uZmlnIGZpbGUpIG9yXG4gIGlubGluZSBwbHVnaW4gb2JqZWN0cy4gV2l0aG91dCBwbHVnaW5zLCBpbnN0cnVtZW50YXRpb24uanNvbiBwb2ludHMgPSBbXS5cblxuRXhhbXBsZXM6XG4gIHRhY3RpY2EgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjIEdlbmVyYXRlIHR5cGVzIHdpdGggZ2xvYmFsIGF1Z21lbnRhdGlvbiAoZGVmYXVsdClcbiAgdGFjdGljYSAtLXdhdGNoICAgICAgICAgICAgICAgICAgICAgICMgV2F0Y2ggbW9kZVxuICB0YWN0aWNhIC0tbW9kdWxlLWF1Z21lbnRhdGlvbiAgICAgICAgIyBVc2UgbGVnYWN5IG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZVxuICB0YWN0aWNhIC0tcHJvamVjdCAuL3NyYy90c2NvbmZpZy5qc29uICMgQ3VzdG9tIHRzY29uZmlnIHBhdGhcbiAgdGFjdGljYSAtLW91dHB1dCAuL3R5cGVzL21uZW1vbmljYSAgICMgQ3VzdG9tIG91dHB1dCBkaXJlY3RvcnlcbiAgdGFjdGljYSAtLXRvcG9sb2dpY2EgLi9zcmMvYWktdHlwZXMgICMgU2NhbiBzcGVjaWZpYyB0b3BvbG9naWNhIGRpcmVjdG9yeVxuYCk7XG59XG5cbi8qKlxuICogRmluZCB0c2NvbmZpZy5qc29uXG4gKi9cbmZ1bmN0aW9uIGZpbmRUc0NvbmZpZyAocHJvamVjdFBhdGg/OiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRpZiAocHJvamVjdFBhdGgpIHtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyhwcm9qZWN0UGF0aCkpIHtcblx0XHRcdHJldHVybiBwcm9qZWN0UGF0aDtcblx0XHR9XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBQcm9qZWN0IGZpbGUgbm90IGZvdW5kOiAke3Byb2plY3RQYXRofWApO1xuXHR9XG5cblx0Ly8gTG9vayBmb3IgdHNjb25maWcuanNvbiBpbiBjdXJyZW50IGRpcmVjdG9yeSBhbmQgcGFyZW50IGRpcmVjdG9yaWVzXG5cdGxldCBjdXJyZW50RGlyID0gcHJvY2Vzcy5jd2QoKTtcblx0d2hpbGUgKGN1cnJlbnREaXIgIT09IHBhdGguZGlybmFtZShjdXJyZW50RGlyKSkge1xuXHRcdGNvbnN0IHRzY29uZmlnUGF0aCA9IHBhdGguam9pbihjdXJyZW50RGlyLCAndHNjb25maWcuanNvbicpO1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKHRzY29uZmlnUGF0aCkpIHtcblx0XHRcdHJldHVybiB0c2NvbmZpZ1BhdGg7XG5cdFx0fVxuXHRcdGN1cnJlbnREaXIgPSBwYXRoLmRpcm5hbWUoY3VycmVudERpcik7XG5cdH1cblxuXHRyZXR1cm4gdW5kZWZpbmVkO1xufVxuXG4vKipcbiAqIExvYWQgVHlwZVNjcmlwdCBwcm9ncmFtIGZyb20gdHNjb25maWdcbiAqL1xuZnVuY3Rpb24gbG9hZFByb2dyYW0gKHRzY29uZmlnUGF0aDogc3RyaW5nKTogdHMuUHJvZ3JhbSB7XG5cdGNvbnN0IGNvbmZpZ0ZpbGUgPSB0cy5yZWFkQ29uZmlnRmlsZSh0c2NvbmZpZ1BhdGgsIHRzLnN5cy5yZWFkRmlsZSk7XG5cblx0aWYgKGNvbmZpZ0ZpbGUuZXJyb3IpIHtcblx0XHRjb25zdCBlcnJvclRleHQgPSB0cy5mbGF0dGVuRGlhZ25vc3RpY01lc3NhZ2VUZXh0KFxuXHRcdFx0Y29uZmlnRmlsZS5lcnJvci5tZXNzYWdlVGV4dCxcblx0XHRcdCdcXG4nXG5cdFx0KTtcblx0XHR0aHJvdyBuZXcgRXJyb3IoYEVycm9yIHJlYWRpbmcgdHNjb25maWc6ICR7ZXJyb3JUZXh0fWApO1xuXHR9XG5cblx0Ly8gVGFjdGljYSBhbmFseXplcyB3aXRoIGl0cyBvd24gYnVuZGxlZCBUeXBlU2NyaXB0LCB3aGljaCBtYXkgYmUgbmV3ZXJcblx0Ly8gdGhhbiB0aGUgY29tcGlsZXIgdGhlIHVzZXIncyB0c2NvbmZpZyB3YXMgd3JpdHRlbiBmb3IgKGUuZy4gYSBUUzUtZXJhXG5cdC8vIGNvbmZpZyBjYXJyeWluZyBgYmFzZVVybGAsIGRlcHJlY2F0ZWQtZXJyb3JlZCBieSBUUzYncyBUUzUxMDEpLlxuXHQvLyBBbmFseXNpcyBuZXZlciBlbWl0cyB1c2VyIGNvZGUsIHNvIGRlcHJlY2F0aW9uIGVycm9ycyBhcmUgYWJvdXQgdGhlXG5cdC8vIHVzZXIncyBidWlsZCBwaXBlbGluZSwgbm90IGFib3V0IGFuYWx5emFiaWxpdHkg4oCUIHNpbGVuY2UgdGhlbSBmb3IgdGhlXG5cdC8vIGFuYWx5c2lzIHByb2dyYW0uIFVuY29uZGl0aW9uYWw6IGEgdXNlci1waW5uZWQgb2xkZXIgdmFsdWUgKCc1LjAnKVxuXHQvLyBkb2VzIG5vdCBzaWxlbmNlIDYuMCBkZXByZWNhdGlvbnMgYW5kIHdvdWxkIHN0aWxsIGZhdGFsIGJlbG93LlxuXHRjb25zdCByYXdDb25maWcgPSBjb25maWdGaWxlLmNvbmZpZyA/PyB7fTtcblx0cmF3Q29uZmlnLmNvbXBpbGVyT3B0aW9ucyA9IHtcblx0XHQuLi5yYXdDb25maWcuY29tcGlsZXJPcHRpb25zLFxuXHRcdGlnbm9yZURlcHJlY2F0aW9ucyA6ICc2LjAnLFxuXHR9O1xuXG5cdGNvbnN0IHBhcnNlZENvbmZpZyA9IHRzLnBhcnNlSnNvbkNvbmZpZ0ZpbGVDb250ZW50KFxuXHRcdHJhd0NvbmZpZyxcblx0XHR0cy5zeXMsXG5cdFx0cGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aClcblx0KTtcblxuXHRpZiAocGFyc2VkQ29uZmlnLmVycm9ycy5sZW5ndGggPiAwKSB7XG5cdFx0Y29uc3QgZXJyb3JNZXNzYWdlcyA9IHBhcnNlZENvbmZpZy5lcnJvcnMubWFwKGUgPT5cblx0XHRcdHRzLmZsYXR0ZW5EaWFnbm9zdGljTWVzc2FnZVRleHQoZS5tZXNzYWdlVGV4dCwgJ1xcbicpKTtcblx0XHR0aHJvdyBuZXcgRXJyb3IoYEVycm9yIHBhcnNpbmcgdHNjb25maWc6ICR7ZXJyb3JNZXNzYWdlcy5qb2luKCdcXG4nKX1gKTtcblx0fVxuXG5cdGNvbnN0IHByb2dyYW0gPSB0cy5jcmVhdGVQcm9ncmFtKHtcblx0XHRyb290TmFtZXMgOiBwYXJzZWRDb25maWcuZmlsZU5hbWVzLFxuXHRcdG9wdGlvbnMgICA6IHBhcnNlZENvbmZpZy5vcHRpb25zLFxuXHR9KTtcblxuXHRyZXR1cm4gcHJvZ3JhbTtcbn1cblxuLyoqXG4gKiBMb29rIHVwIGEgdmFyaWFibGUgYnkgbmFtZSBzdGFydGluZyBmcm9tIGEgc2NvcGUsIHdhbGtpbmcgb3V0d2FyZCB0aHJvdWdoXG4gKiBwYXJlbnRTY29wZUlkLiBUaGUgaW5uZXJtb3N0IGJpbmRpbmcgd2lucyBldmVuIHdoZW4gaXQgY2FycmllcyBubyB0eXBlUGF0aFxuICogKHNoYWRvd2luZyBob25lc3R5IOKAlCBhbiB1bnR5cGVkIGxvY2FsIHNoYWRvd3MgYSB0eXBlZCBvdXRlciBvbmUpLlxuICovXG5mdW5jdGlvbiByZXNvbHZlU2NvcGVkVmFyaWFibGVUeXBlUGF0aCAoXG5cdG5hbWU6IHN0cmluZyxcblx0c2NvcGVJZDogc3RyaW5nLFxuXHRzY29wZUFuYWx5c2lzOiBTY29wZUFuYWx5c2lzXG4pOiBzdHJpbmcgfCB1bmRlZmluZWQge1xuXHRsZXQgY3VycmVudDogc3RyaW5nIHwgdW5kZWZpbmVkID0gc2NvcGVJZDtcblx0d2hpbGUgKGN1cnJlbnQpIHtcblx0XHRjb25zdCB2YXJpYWJsZSA9IHNjb3BlQW5hbHlzaXMudmFyaWFibGVzLmdldChgJHtjdXJyZW50fSMke25hbWV9YCk7XG5cdFx0aWYgKHZhcmlhYmxlKSB7XG5cdFx0XHRjb25zdCB7IHR5cGVQYXRoIH0gPSB2YXJpYWJsZTtcblx0XHRcdHJldHVybiB0eXBlUGF0aDtcblx0XHR9XG5cdFx0Y3VycmVudCA9IHNjb3BlQW5hbHlzaXMuc2NvcGVzLmdldChjdXJyZW50KT8ucGFyZW50U2NvcGVJZDtcblx0fVxuXHRyZXR1cm4gdW5kZWZpbmVkO1xufVxuXG4vKipcbiAqIEpvaW4gZGF0YSBmb3IgbW5lbW9ncmFwaGljYSdzIHdyYXBwZXJzIGxheWVyOiBwaW4gZWFjaCB3cmFwIGVudHJ5IHRvIHRoZVxuICogc2NvcGUgaG9sZGluZyBpdHMgY2FsbCBzaXRlLCBhbmQgcmVzb2x2ZSB0aGUgd3JhcHBlZCBpbnN0YW5jZSBhcmd1bWVudCdzXG4gKiBtbmVtb25pY2EgdHlwZSB0aHJvdWdoIHRoZSBzY29wZS12YXJpYWJsZSBjaGFpbi5cbiAqL1xuZnVuY3Rpb24gYXR0YWNoV3JhcEpvaW5EYXRhIChcblx0ZWRzOiBNYXA8c3RyaW5nLCBFRFNJbmZvW10+LFxuXHRzY29wZVdhbGtlcjogTG9jYWxTY29wZVdhbGtlcixcblx0c2NvcGVBbmFseXNpczogU2NvcGVBbmFseXNpc1xuKTogdm9pZCB7XG5cdGZvciAoY29uc3QgZW50cmllcyBvZiBlZHMudmFsdWVzKCkpIHtcblx0XHRmb3IgKGNvbnN0IGVudHJ5IG9mIGVudHJpZXMpIHtcblx0XHRcdGlmIChlbnRyeS5raW5kICE9PSAnd3JhcCcpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBob2xkZXJTY29wZUlkID0gc2NvcGVXYWxrZXIuZmluZEhvbGRlclNjb3BlSWQoZW50cnkubG9jYXRpb24pO1xuXHRcdFx0aWYgKCFob2xkZXJTY29wZUlkKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0ZW50cnkuc2NvcGVJZCA9IGhvbGRlclNjb3BlSWQ7XG5cdFx0XHRpZiAoIWVudHJ5Lmluc3RhbmNlQXJnKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3Qgd3JhcHNUeXBlUGF0aCA9IHJlc29sdmVTY29wZWRWYXJpYWJsZVR5cGVQYXRoKFxuXHRcdFx0XHRlbnRyeS5pbnN0YW5jZUFyZyxcblx0XHRcdFx0aG9sZGVyU2NvcGVJZCxcblx0XHRcdFx0c2NvcGVBbmFseXNpc1xuXHRcdFx0KTtcblx0XHRcdGlmICh3cmFwc1R5cGVQYXRoKSB7XG5cdFx0XHRcdGVudHJ5LndyYXBzVHlwZVBhdGggPSB3cmFwc1R5cGVQYXRoO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxufVxuXG4vKipcbiAqIFJlbmRlciB0eXBlIGhpZXJhcmNoeSBhcyBhbiBBU0NJSSB0cmVlIHN0cmluZy5cbiAqIERpc3BsYXktb25seTogc2libGluZ3MgYXJlIHNvcnRlZCBieSBmdWxsUGF0aCBhdCByZW5kZXIgdGltZSAoY29kZS11bml0XG4gKiBvcmRlciDigJQgZGVmYXVsdC1jb2xsZWN0aW9uIFBhc2NhbENhc2Ugcm9vdHMgbGFuZCBiZWZvcmUgdGhlXG4gKiBgY29sbGVjdGlvbl9OOjpgLXByZWZpeGVkIG9uZXMpLiBUaGUgZ3JhcGggaXRzZWxmIGtlZXBzIGRpc2NvdmVyeSBvcmRlcjtcbiAqIGhpZXJhcmNoeS5qc29uIGlzIHVuYWZmZWN0ZWQuXG4gKi9cbmZ1bmN0aW9uIHJlbmRlclR5cGVIaWVyYXJjaHkgKGdyYXBoOiBUeXBlR3JhcGhJbXBsKTogc3RyaW5nIHtcblx0Y29uc3QgbGluZXM6IHN0cmluZ1tdID0gWyAnVHlwZSBIaWVyYXJjaHkgKFRyaWUpOicgXTtcblxuXHRmdW5jdGlvbiBzb3J0ZWRCeUZ1bGxQYXRoIChub2RlczogVHlwZU5vZGVbXSk6IFR5cGVOb2RlW10ge1xuXHRcdGNvbnN0IHNvcnRlZCA9IEFycmF5LmZyb20obm9kZXMpO1xuXHRcdHNvcnRlZC5zb3J0KChhLCBiKSA9PiB7XG5cdFx0XHRpZiAoYS5mdWxsUGF0aCA8IGIuZnVsbFBhdGgpIHsgcmV0dXJuIC0xOyB9XG5cdFx0XHRpZiAoYS5mdWxsUGF0aCA+IGIuZnVsbFBhdGgpIHsgcmV0dXJuIDE7IH1cblx0XHRcdHJldHVybiAwO1xuXHRcdH0pO1xuXHRcdHJldHVybiBzb3J0ZWQ7XG5cdH1cblxuXHRmdW5jdGlvbiByZW5kZXJOb2RlIChub2RlOiBUeXBlTm9kZSwgcHJlZml4ID0gJycsIGlzTGFzdCA9IHRydWUpOiB2b2lkIHtcblx0XHRjb25zdCBjb25uZWN0b3IgPSBpc0xhc3QgPyAn4pSU4pSA4pSAICcgOiAn4pSc4pSA4pSAICc7XG5cdFx0Ly8gVXNlIG5vZGUuZnVsbFBhdGggZGlyZWN0bHkgYW5kIGNvbnZlcnQgZG90cyB0byB1bmRlcnNjb3Jlc1xuXHRcdGNvbnN0IGluc3RhbmNlTmFtZSA9IG5vZGUuZnVsbFBhdGgucmVwbGFjZSgvXFwuL2csICdfJyk7XG5cdFx0bGluZXMucHVzaChgJHtwcmVmaXh9JHtjb25uZWN0b3J9JHtpbnN0YW5jZU5hbWV9YCk7XG5cblx0XHRjb25zdCBjaGlsZHJlbiA9IHNvcnRlZEJ5RnVsbFBhdGgoQXJyYXkuZnJvbShub2RlLmNoaWxkcmVuLnZhbHVlcygpKSk7XG5cdFx0Y29uc3QgbmV3UHJlZml4ID0gcHJlZml4ICsgKGlzTGFzdCA/ICcgICAgJyA6ICfilIIgICAnKTtcblxuXHRcdGZvciAobGV0IGkgPSAwOyBpIDwgY2hpbGRyZW4ubGVuZ3RoOyBpKyspIHtcblx0XHRcdHJlbmRlck5vZGUoY2hpbGRyZW5bIGkgXSwgbmV3UHJlZml4LCBpID09PSBjaGlsZHJlbi5sZW5ndGggLSAxKTtcblx0XHR9XG5cdH1cblxuXHRjb25zdCByb290cyA9IHNvcnRlZEJ5RnVsbFBhdGgoQXJyYXkuZnJvbShncmFwaC5yb290cy52YWx1ZXMoKSkpO1xuXHRmb3IgKGxldCBpID0gMDsgaSA8IHJvb3RzLmxlbmd0aDsgaSsrKSB7XG5cdFx0cmVuZGVyTm9kZShyb290c1sgaSBdLCAnJywgaSA9PT0gcm9vdHMubGVuZ3RoIC0gMSk7XG5cdH1cblx0Ly8gRW1wdHkgbGluZSBhdCBlbmRcblx0bGluZXMucHVzaCgnJyk7XG5cblx0Y29uc3QgcmVzdWx0ID0gbGluZXMuam9pbignXFxuJyk7XG5cdHJldHVybiByZXN1bHQ7XG59XG5cbi8qKlxuICogUHJpbnQgdHlwZSBoaWVyYXJjaHkgdG8gdGhlIGNvbnNvbGUuXG4gKi9cbmZ1bmN0aW9uIHByaW50VHlwZUhpZXJhcmNoeSAoZ3JhcGg6IFR5cGVHcmFwaEltcGwpOiB2b2lkIHtcblx0Y29uc3Qgb3V0cHV0ID0gcmVuZGVyVHlwZUhpZXJhcmNoeShncmFwaCk7XG5cdGNvbnNvbGUubG9nKG91dHB1dCk7XG59XG5cbi8qKlxuICogQ2hlY2sgaWYgQG1uZW1vbmljYS9kaXZlIGlzIHByZXNlbnQgaW4gcGFja2FnZS5qc29uIGRlcGVuZGVuY2llc1xuICovXG5mdW5jdGlvbiBoYXNEaXZlRGVwZW5kZW5jeSAocHJvamVjdERpcjogc3RyaW5nKTogYm9vbGVhbiB7XG5cdGNvbnN0IHBhY2thZ2VKc29uUGF0aCA9IHBhdGguam9pbihwcm9qZWN0RGlyLCAncGFja2FnZS5qc29uJyk7XG5cdGlmICghZnMuZXhpc3RzU3luYyhwYWNrYWdlSnNvblBhdGgpKSB7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG5cdHRyeSB7XG5cdFx0Y29uc3QgY29udGVudCA9IGZzLnJlYWRGaWxlU3luYyhwYWNrYWdlSnNvblBhdGgsICd1dGYtOCcpO1xuXHRcdGNvbnN0IHBrZyA9IEpTT04ucGFyc2UoY29udGVudCk7XG5cdFx0Y29uc3QgZGVwcyA9IHBrZy5kZXBlbmRlbmNpZXMgfHwge307XG5cdFx0Y29uc3QgZGV2RGVwcyA9IHBrZy5kZXZEZXBlbmRlbmNpZXMgfHwge307XG5cdFx0Y29uc3QgcGVlckRlcHMgPSBwa2cucGVlckRlcGVuZGVuY2llcyB8fCB7fTtcblx0XHRyZXR1cm4gJ0BtbmVtb25pY2EvZGl2ZScgaW4gZGVwcyB8fCAnQG1uZW1vbmljYS9kaXZlJyBpbiBkZXZEZXBzIHx8ICdAbW5lbW9uaWNhL2RpdmUnIGluIHBlZXJEZXBzO1xuXHR9IGNhdGNoIHtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cbn1cblxuLyoqXG4gKiBTY2FuIGZvciB0b3BvbG9naWNhIGRpcmVjdG9yeSBzdHJ1Y3R1cmVzXG4gKi9cbmZ1bmN0aW9uIHNjYW5Ub3BvbG9naWNhRGlyZWN0b3JpZXMgKHByb2plY3REaXI6IHN0cmluZywgY3VzdG9tRGlycz86IHN0cmluZ1tdKTogc3RyaW5nW10ge1xuXHRjb25zdCBkaXJzOiBzdHJpbmdbXSA9IFtdO1xuXG5cdC8vIEZpcnN0LCBhZGQgY3VzdG9tIGRpcmVjdG9yaWVzIGlmIHNwZWNpZmllZFxuXHRpZiAoY3VzdG9tRGlycykge1xuXHRcdGZvciAoY29uc3QgZGlyIG9mIGN1c3RvbURpcnMpIHtcblx0XHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmlzQWJzb2x1dGUoZGlyKSA/IGRpciA6IHBhdGguam9pbihwcm9qZWN0RGlyLCBkaXIpO1xuXHRcdFx0aWYgKGZzLmV4aXN0c1N5bmMoZGlyUGF0aCkgJiYgZnMuc3RhdFN5bmMoZGlyUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRjb25zb2xlLndhcm4oYFdhcm5pbmc6IFRvcG9sb2dpY2EgZGlyZWN0b3J5IG5vdCBmb3VuZDogJHtkaXJQYXRofWApO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8vIFRoZW4gYXV0by1kaXNjb3ZlciBzdGFuZGFyZCB0b3BvbG9naWNhIGRpcmVjdG9yaWVzXG5cdGNvbnN0IHBvc3NpYmxlRGlycyA9IFsgJ2FpLXR5cGVzJywgJ3R5cGVzJywgJ3RvcG9sb2dpY2EtdHlwZXMnIF07XG5cblx0Zm9yIChjb25zdCBkaXJOYW1lIG9mIHBvc3NpYmxlRGlycykge1xuXHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgZGlyTmFtZSk7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmMoZGlyUGF0aCkgJiYgZnMuc3RhdFN5bmMoZGlyUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0Ly8gQXZvaWQgZHVwbGljYXRlc1xuXHRcdFx0aWYgKCFkaXJzLmluY2x1ZGVzKGRpclBhdGgpKSB7XG5cdFx0XHRcdGRpcnMucHVzaChkaXJQYXRoKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvLyBBbHNvIHNjYW4gc3JjLyBzdWJkaXJlY3Rvcnlcblx0Y29uc3Qgc3JjUGF0aCA9IHBhdGguam9pbihwcm9qZWN0RGlyLCAnc3JjJyk7XG5cdGlmIChmcy5leGlzdHNTeW5jKHNyY1BhdGgpICYmIGZzLnN0YXRTeW5jKHNyY1BhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRmb3IgKGNvbnN0IGRpck5hbWUgb2YgcG9zc2libGVEaXJzKSB7XG5cdFx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5qb2luKHNyY1BhdGgsIGRpck5hbWUpO1xuXHRcdFx0aWYgKGZzLmV4aXN0c1N5bmMoZGlyUGF0aCkgJiYgZnMuc3RhdFN5bmMoZGlyUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdFx0XHQvLyBBdm9pZCBkdXBsaWNhdGVzXG5cdFx0XHRcdGlmICghZGlycy5pbmNsdWRlcyhkaXJQYXRoKSkge1xuXHRcdFx0XHRcdGRpcnMucHVzaChkaXJQYXRoKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdHJldHVybiBkaXJzO1xufVxuXG4vKipcbiAqIENvbmZpZyBmaWxlIGNhbmRpZGF0ZXMgKGVzbGludC1zdHlsZSBwcm9qZWN0IGNvbmZpZyksIHNlYXJjaGVkIG5leHQgdG9cbiAqIHRoZSByZXNvbHZlZCB0c2NvbmZpZyBmaXJzdCwgdGhlbiBpbiB0aGUgY3VycmVudCB3b3JraW5nIGRpcmVjdG9yeS5cbiAqL1xuY29uc3QgQ09ORklHX0ZJTEVfTkFNRVMgPSBbICcudGFjdGljYS5qcycsICd0YWN0aWNhLmNvbmZpZy5qcycgXTtcblxuaW50ZXJmYWNlIFRhY3RpY2FDb25maWdGaWxlIHtcblx0cGx1Z2lucz86IEFycmF5PFRhY3RpY2FQbHVnaW4gfCBzdHJpbmc+O1xufVxuXG4vKipcbiAqIExvYWQgZnJhbWV3b3JrLXZvY2FidWxhcnkgcGx1Z2luczogcHJvZ3JhbW1hdGljIG9wdGlvbnMgZmlyc3QsIHRoZW4gdGhlXG4gKiBwcm9qZWN0IGNvbmZpZyBmaWxlLiBTdHJpbmcgZW50cmllcyBhcmUgbW9kdWxlIHNwZWNpZmllcnMgcmVxdWlyZWRcbiAqIHJlbGF0aXZlIHRvIHRoZSBjb25maWcgZmlsZSAoZS5nLiBhbiBhZGFwdGVyIHBhY2thZ2UncyBwbHVnaW4gc3VicGF0aCkuXG4gKiBXaXRob3V0IGEgY29uZmlnIGZpbGUgYW5kIHdpdGhvdXQgcHJvZ3JhbW1hdGljIHBsdWdpbnMgdGhlIGFuYWx5emVyXG4gKiBzdGF5cyBmcmFtZXdvcmstYmxpbmQgYW5kIGluc3RydW1lbnRhdGlvbi5qc29uIGNhcnJpZXMgZW1wdHkgcG9pbnRzLlxuICovXG5mdW5jdGlvbiBsb2FkVGFjdGljYVBsdWdpbnMgKHByb2plY3REaXI6IHN0cmluZywgb3B0aW9uczogQ0xJT3B0aW9ucyk6IFRhY3RpY2FQbHVnaW5bXSB7XG5cdGNvbnN0IHBsdWdpbnM6IFRhY3RpY2FQbHVnaW5bXSA9IFsgLi4uKG9wdGlvbnMucGx1Z2lucyB8fCBbXSkgXTtcblxuXHRjb25zdCBzZWFyY2hEaXJzID0gWyBwcm9qZWN0RGlyIF07XG5cdGNvbnN0IGN3ZCA9IHByb2Nlc3MuY3dkKCk7XG5cdGlmIChjd2QgIT09IHByb2plY3REaXIpIHtcblx0XHRzZWFyY2hEaXJzLnB1c2goY3dkKTtcblx0fVxuXG5cdGxldCBjb25maWdQYXRoOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdGZvciAoY29uc3QgZGlyIG9mIHNlYXJjaERpcnMpIHtcblx0XHRmb3IgKGNvbnN0IG5hbWUgb2YgQ09ORklHX0ZJTEVfTkFNRVMpIHtcblx0XHRcdGNvbnN0IGNhbmRpZGF0ZSA9IHBhdGguam9pbihkaXIsIG5hbWUpO1xuXHRcdFx0aWYgKGZzLmV4aXN0c1N5bmMoY2FuZGlkYXRlKSkge1xuXHRcdFx0XHRjb25maWdQYXRoID0gY2FuZGlkYXRlO1xuXHRcdFx0XHRicmVhaztcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKGNvbmZpZ1BhdGgpIHtcblx0XHRcdGJyZWFrO1xuXHRcdH1cblx0fVxuXG5cdGlmICghY29uZmlnUGF0aCkge1xuXHRcdHJldHVybiBwbHVnaW5zO1xuXHR9XG5cblx0Ly8gY3JlYXRlUmVxdWlyZSBhbmNob3JlZCBhdCB0aGUgY29uZmlnIGZpbGU6IHRoZSBjb25maWcncyBvd24gaW1wb3J0c1xuXHQvLyBhbmQgc3RyaW5nIHBsdWdpbiBzcGVjaWZpZXJzIHJlc29sdmUgYWdhaW5zdCB0aGUgcHJvamVjdCdzIG1vZHVsZXNcblx0Y29uc3QgY29uZmlnUmVxdWlyZSA9IGNyZWF0ZVJlcXVpcmUoY29uZmlnUGF0aCk7XG5cdGNvbnN0IGxvYWRlZCA9IGNvbmZpZ1JlcXVpcmUoY29uZmlnUGF0aCk7XG5cdGNvbnN0IGNvbmZpZzogVGFjdGljYUNvbmZpZ0ZpbGUgPSBsb2FkZWQgJiYgdHlwZW9mIGxvYWRlZCA9PT0gJ29iamVjdCcgJiYgJ2RlZmF1bHQnIGluIGxvYWRlZFxuXHRcdD8gbG9hZGVkLmRlZmF1bHRcblx0XHQ6IGxvYWRlZDtcblx0Y29uc3QgZW50cmllcyA9IGNvbmZpZyAmJiBBcnJheS5pc0FycmF5KGNvbmZpZy5wbHVnaW5zKSA/IGNvbmZpZy5wbHVnaW5zIDogW107XG5cblx0Zm9yIChjb25zdCBlbnRyeSBvZiBlbnRyaWVzKSB7XG5cdFx0aWYgKHR5cGVvZiBlbnRyeSAhPT0gJ3N0cmluZycpIHtcblx0XHRcdHBsdWdpbnMucHVzaChlbnRyeSk7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cdFx0Y29uc3QgbW9kID0gY29uZmlnUmVxdWlyZShlbnRyeSk7XG5cdFx0Y29uc3QgcGx1Z2luOiBUYWN0aWNhUGx1Z2luID0gbW9kICYmIHR5cGVvZiBtb2QgPT09ICdvYmplY3QnICYmICdkZWZhdWx0JyBpbiBtb2Rcblx0XHRcdD8gbW9kLmRlZmF1bHRcblx0XHRcdDogbW9kO1xuXHRcdHBsdWdpbnMucHVzaChwbHVnaW4pO1xuXHR9XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IG5hbWVzID0gcGx1Z2lucy5tYXAocGx1Z2luID0+IHBsdWdpbi5uYW1lIHx8ICcodW5uYW1lZCknKS5qb2luKCcsICcpO1xuXHRcdGNvbnNvbGUubG9nKGBMb2FkZWQgdGFjdGljYSBjb25maWc6ICR7Y29uZmlnUGF0aH0gKHBsdWdpbnM6ICR7bmFtZXMgfHwgJ25vbmUnfSlgKTtcblx0fVxuXG5cdHJldHVybiBwbHVnaW5zO1xufVxuXG4vKipcbiAqIFJ1biB0eXBlIGdlbmVyYXRpb24uIFJldHVybnMgMCBvbiBzdWNjZXNzOyAxIHdoZW4gdGhlIGdyYXBoIGlkZW50aXR5IGxhd1xuICogYWJvcnRlZCB0aGUgcnVuIChmYWlsdXJlcyBwcmludGVkLCBubyAudGFjdGljYSBvdXRwdXQgd3JpdHRlbikuXG4gKi9cbmZ1bmN0aW9uIHJ1biAob3B0aW9uczogQ0xJT3B0aW9ucyk6IG51bWJlciB7XG5cdGNvbnN0IHRzY29uZmlnUGF0aCA9IGZpbmRUc0NvbmZpZyhvcHRpb25zLnByb2plY3QpO1xuXG5cdGlmICghdHNjb25maWdQYXRoKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6IENvdWxkIG5vdCBmaW5kIHRzY29uZmlnLmpzb24nKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYFVzaW5nIHRzY29uZmlnOiAke3RzY29uZmlnUGF0aH1gKTtcblx0fVxuXG5cdC8vIEZyYW1ld29yayB2b2NhYnVsYXJ5IGFycml2ZXMgdmlhIHBsdWdpbnMg4oCUIGEgY29uZmlnIGZpbGUgbmV4dCB0byB0aGVcblx0Ly8gdHNjb25maWcgKG9yIGluIGN3ZCkgYW5kL29yIHByb2dyYW1tYXRpYyBvcHRpb25zLiBOb25lIGxvYWRlZCBtZWFuc1xuXHQvLyB0aGUgYW5hbHl6ZXIgZGV0ZWN0cyB6ZXJvIGluc3RydW1lbnRhdGlvbiBwb2ludHMuXG5cdGNvbnN0IHBsdWdpbnMgPSBsb2FkVGFjdGljYVBsdWdpbnMocGF0aC5kaXJuYW1lKHBhdGgucmVzb2x2ZSh0c2NvbmZpZ1BhdGgpKSwgb3B0aW9ucyk7XG5cblx0Ly8gTG9hZCBUeXBlU2NyaXB0IHByb2dyYW1cblx0Y29uc3QgcHJvZ3JhbSA9IGxvYWRQcm9ncmFtKHRzY29uZmlnUGF0aCk7XG5cblx0Ly8gQ3JlYXRlIGFuYWx5emVyXG5cdGNvbnN0IGFuYWx5emVyID0gbmV3IE1uZW1vbmljYUFuYWx5emVyKHByb2dyYW0sIHBsdWdpbnMpO1xuXG5cdC8vIERldGVybWluZSBvdXRwdXQgZGlyZWN0b3J5IGZvciBleGNsdXNpb25cblx0Y29uc3Qgb3V0cHV0RGlyID0gb3B0aW9ucy5vdXRwdXREaXIgfHwgJy50YWN0aWNhJztcblx0Y29uc3Qgb3V0cHV0RGlyUGF0aCA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBvdXRwdXREaXIpO1xuXHQvLyBUaGUgcHJvamVjdC1jb252ZW50aW9uYWwgLnRhY3RpY2EgZGlyIChuZXh0IHRvIHRzY29uZmlnKSBpcyBBTFdBWVNcblx0Ly8gZXhjbHVkZWQsIGV2ZW4gd2hlbiAtLW91dHB1dCBwb2ludHMgZWxzZXdoZXJlOiBnZW5lcmF0ZWQgZmlsZXMgYXJlXG5cdC8vIG5ldmVyIHByb2plY3Qgc291cmNlLiByZXNvbHZlKCkgYm90aCBzaWRlcyDigJQgdHNjb25maWdQYXRoIG1heSBiZVxuXHQvLyByZWxhdGl2ZSAoJy4vdHNjb25maWcuanNvbicpIHdoaWxlIHNvdXJjZUZpbGUuZmlsZU5hbWUgaXMgYWJzb2x1dGVcblx0Y29uc3QgY29udmVudGlvbmFsT3V0cHV0RGlyID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpLCAnLnRhY3RpY2EnKTtcblxuXHQvLyBDb2xsZWN0IHNvdXJjZSBmaWxlcyB0byBhbmFseXplXG5cdGNvbnN0IHNvdXJjZUZpbGVzOiB0cy5Tb3VyY2VGaWxlW10gPSBbXTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHByb2dyYW0uZ2V0U291cmNlRmlsZXMoKSkge1xuXHRcdGlmIChzb3VyY2VGaWxlLmlzRGVjbGFyYXRpb25GaWxlKSB7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cblx0XHRjb25zdCBhYnNvbHV0ZUZpbGVOYW1lID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdGlmIChhYnNvbHV0ZUZpbGVOYW1lLnN0YXJ0c1dpdGgob3V0cHV0RGlyUGF0aCArIHBhdGguc2VwKSB8fFxuXHRcdFx0YWJzb2x1dGVGaWxlTmFtZS5zdGFydHNXaXRoKGNvbnZlbnRpb25hbE91dHB1dERpciArIHBhdGguc2VwKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZXhjbHVkZSBwYXR0ZXJuc1xuXHRcdGlmIChvcHRpb25zLmV4Y2x1ZGUpIHtcblx0XHRcdGNvbnN0IHNob3VsZEV4Y2x1ZGUgPSBvcHRpb25zLmV4Y2x1ZGUuc29tZShwYXR0ZXJuID0+XG5cdFx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUuaW5jbHVkZXMocGF0dGVybi5yZXBsYWNlKC9cXCovZywgJycpKSk7XG5cdFx0XHRpZiAoc2hvdWxkRXhjbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBDaGVjayBpbmNsdWRlIHBhdHRlcm5zXG5cdFx0aWYgKG9wdGlvbnMuaW5jbHVkZSAmJiBvcHRpb25zLmluY2x1ZGUubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3Qgc2hvdWxkSW5jbHVkZSA9IG9wdGlvbnMuaW5jbHVkZS5zb21lKHBhdHRlcm4gPT5cblx0XHRcdFx0c291cmNlRmlsZS5maWxlTmFtZS5pbmNsdWRlcyhwYXR0ZXJuLnJlcGxhY2UoL1xcKi9nLCAnJykpKTtcblx0XHRcdGlmICghc2hvdWxkSW5jbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRzb3VyY2VGaWxlcy5wdXNoKHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0Ly8gU2NhbiBmb3IgdG9wb2xvZ2ljYSBkaXJlY3Rvcnkgc3RydWN0dXJlcyBGSVJTVFxuXHRjb25zdCBwcm9qZWN0RGlyID0gcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCk7XG5cdGNvbnN0IHRvcG9sb2dpY2FEaXJzID0gc2NhblRvcG9sb2dpY2FEaXJlY3Rvcmllcyhwcm9qZWN0RGlyLCBvcHRpb25zLnRvcG9sb2dpY2FEaXJzKTtcblxuXHRpZiAodG9wb2xvZ2ljYURpcnMubGVuZ3RoID4gMCAmJiBvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgRm91bmQgdG9wb2xvZ2ljYSBkaXJlY3RvcmllczogJHt0b3BvbG9naWNhRGlycy5qb2luKCcsICcpfWApO1xuXHR9XG5cblx0Ly8gQW5hbHl6ZSB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIEJFRk9SRSB1c2FnZSBjb2xsZWN0aW9uXG5cdGNvbnN0IHRvcG9sb2dpY2FBbmFseXplciA9IG5ldyBUb3BvbG9naWNhQW5hbHl6ZXIoKTtcblx0Y29uc3QgdG9wb2xvZ2ljYVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIGltcG9ydCgnLi90eXBlcycpLlR5cGVOb2RlPigpO1xuXHRmb3IgKGNvbnN0IGRpciBvZiB0b3BvbG9naWNhRGlycykge1xuXHRcdGNvbnN0IHJlc3VsdCA9IHRvcG9sb2dpY2FBbmFseXplci5hbmFseXplRGlyZWN0b3J5KGRpcik7XG5cdFx0aWYgKHJlc3VsdC50eXBlcy5zaXplID4gMCkge1xuXHRcdFx0Ly8gQ29sbGVjdCB0b3BvbG9naWNhIHR5cGVzIGZvciBkZWZpbml0aW9ucyBhbmQgdXNhZ2UgdHJhY2tpbmdcblx0XHRcdGZvciAoY29uc3QgWyB0eXBlUGF0aCwgbm9kZSBdIG9mIHJlc3VsdC50eXBlcykge1xuXHRcdFx0XHR0b3BvbG9naWNhVHlwZXMuc2V0KHR5cGVQYXRoLCBub2RlKTtcblx0XHRcdH1cblx0XHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdFx0Y29uc29sZS5sb2coYEFkZGVkICR7cmVzdWx0LnR5cGVzLnNpemV9IHR5cGVzIGZyb20gJHtkaXJ9YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChyZXN1bHQuZXJyb3JzLmxlbmd0aCA+IDAgJiYgb3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRyZXN1bHQuZXJyb3JzLmZvckVhY2goZXJyID0+IGNvbnNvbGUud2FybihgW1RvcG9sb2dpY2FdICR7ZXJyfWApKTtcblx0XHR9XG5cdH1cblxuXHQvLyBBZGQgdG9wb2xvZ2ljYSB0eXBlcyB0byBhbmFseXplciBzbyB0aGV5J3JlIGF2YWlsYWJsZSBmb3IgdXNhZ2UgZGV0ZWN0aW9uXG5cdC8vIFByb2Nlc3MgaW4gb3JkZXIgb2YgcGF0aCBkZXB0aCAocGFyZW50cyBmaXJzdCkgdG8gZW5zdXJlIHByb3BlciBoaWVyYXJjaHlcblx0Y29uc3Qgc29ydGVkVHlwZXMgPSBBcnJheS5mcm9tKHRvcG9sb2dpY2FUeXBlcy5lbnRyaWVzKCkpLnNvcnQoKGEsIGIpID0+IHtcblx0XHRjb25zdCBkZXB0aEEgPSAoYVsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRjb25zdCBkZXB0aEIgPSAoYlsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRyZXR1cm4gZGVwdGhBIC0gZGVwdGhCO1xuXHR9KTtcblx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBub2RlIF0gb2Ygc29ydGVkVHlwZXMpIHtcblx0XHRhbmFseXplci5hZGRUb3BvbG9naWNhVHlwZSh0eXBlUGF0aCwgbm9kZSk7XG5cdH1cblxuXHQvLyBGaXJzdCBwYXNzOiBjb2xsZWN0IGFsbCBkZWZpbml0aW9ucy5cblx0Ly8gTW9kdWxlLXNjb3BlIHRyYWNraW5nIChpbXBvcnRzL2V4cG9ydHMgZm9yIG1vZHVsZXMuanNvbikgaGFwcGVucyBpbiB0aGVcblx0Ly8gc2FtZSBwYXNzIOKAlCBpdCBuZWVkcyBvbmx5IHRoZSBBU1QsIG5vdCB0aGUgY29sbGVjdGVkIGRlZmluaXRpb25zLlxuXHRjb25zdCBtb2R1bGVHcmFwaEJ1aWxkZXIgPSBuZXcgTW9kdWxlR3JhcGhCdWlsZGVyKHByb2dyYW0pO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgQW5hbHl6aW5nIChkZWZpbml0aW9ucyk6ICR7c291cmNlRmlsZS5maWxlTmFtZX1gKTtcblx0XHR9XG5cblx0XHR0cnkge1xuXHRcdFx0YW5hbHl6ZXIuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0XHRtb2R1bGVHcmFwaEJ1aWxkZXIuYWRkRmlsZShzb3VyY2VGaWxlKTtcblx0XHR9IGNhdGNoIChlcnIpIHtcblx0XHRcdGNvbnNvbGUuZXJyb3IoYEVycm9yIGFuYWx5emluZyAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OmAsIGVycik7XG5cdFx0XHR0aHJvdyBlcnI7XG5cdFx0fVxuXHR9XG5cblx0Ly8gU2Vjb25kIHBhc3M6IGNvbGxlY3QgdXNhZ2VzIChub3cgYWxsIGRlZmluaXRpb25zIGFyZSBrbm93biwgaW5jbHVkaW5nIHRvcG9sb2dpY2EpXG5cdGFuYWx5emVyLnJlc2V0VXNhZ2VzKCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBBbmFseXppbmcgKHVzYWdlcyk6ICR7c291cmNlRmlsZS5maWxlTmFtZX1gKTtcblx0XHR9XG5cblx0XHR0cnkge1xuXHRcdFx0YW5hbHl6ZXIuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0XHRjb25zb2xlLmVycm9yKGBFcnJvciBhbmFseXppbmcgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfTpgLCBlcnIpO1xuXHRcdFx0dGhyb3cgZXJyO1xuXHRcdH1cblx0fVxuXG5cdC8vIEdlbmVyYXRlIHR5cGVzIGZyb20gbW5lbW9uaWNhIGFuYWx5c2lzXG5cdC8vIE5vdGU6IHRvcG9sb2dpY2EgdHlwZXMgYXJlIGFscmVhZHkgYWRkZWQgdG8gdGhlIGFuYWx5emVyJ3MgZ3JhcGggdmlhIGFkZFRvcG9sb2dpY2FUeXBlKClcblx0Y29uc3QgZ3JhcGggPSBhbmFseXplci5nZXRHcmFwaCgpO1xuXG5cdC8vIFBhdGgtYXdhcmUgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb24gKGlkZW50aXR5IGxhdyk6IHRoZSBnZW5lcmF0b3Jcblx0Ly8gcmVzb2x2ZXMgbmFtZXMgdGhyb3VnaCB0aGUgc2FtZSByZWxhdGl2ZS1maXJzdC9yb290L3VuaXF1ZSB0aWVycyB0aGVcblx0Ly8gYW5hbHl6ZXIgdXNlczsgdGhlIGFuYWx5emVyJ3Mgb3duIHZhbHVlL2ltcG9ydCB0aWVycyBhbHJlYWR5IHZldHRlZCB0aGVcblx0Ly8gdHlwZSBzdHJpbmdzIGR1cmluZyBleHRyYWN0aW9uXG5cdGNvbnN0IHJlZmVyZW5jZVJlc29sdmVyOiBHcmFwaFJlZmVyZW5jZVJlc29sdmVyID0gKHNpbXBsZU5hbWUsIGFuY2hvcikgPT4ge1xuXHRcdGNvbnN0IHJlZlJlc3VsdCA9IHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UoZ3JhcGgsIHNpbXBsZU5hbWUsIGFuY2hvcik7XG5cdFx0aWYgKHJlZlJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRyZXR1cm4gcmVmUmVzdWx0Lm5vZGU7XG5cdFx0fVxuXHRcdGlmIChyZWZSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0cmV0dXJuICdhbWJpZ3VvdXMnO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9O1xuXHRjb25zdCBnZW5lcmF0b3IgPSBuZXcgVHlwZXNHZW5lcmF0b3IoZ3JhcGgsIG9wdGlvbnMuZXNtLCBvcHRpb25zLm91dHB1dERpciwgcmVmZXJlbmNlUmVzb2x2ZXIpO1xuXG5cdC8vIENoZWNrIGlmIG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZSBpcyByZXF1ZXN0ZWQgKGxlZ2FjeSlcblx0Y29uc3QgdXNlTW9kdWxlQXVnbWVudGF0aW9uID0gb3B0aW9ucy5nbG9iYWxBdWdtZW50YXRpb24gPT09IGZhbHNlO1xuXG5cdC8vIEdlbmVyYXRlIGV2ZXJ5dGhpbmcgaW50byBtZW1vcnkgRklSU1Qg4oCUIHRoZSBoYXJkLWZhaWwgbGF3IGJlbG93IG1heVxuXHQvLyBhYm9ydCB0aGUgcnVuLCBhbmQgbm8gLnRhY3RpY2Egb3V0cHV0IGF0IGFsbCBtYXkgYmUgd3JpdHRlbiB0aGVuXG5cdGxldCBnZW5lcmF0ZWRUeXBlczogeyBjb250ZW50OiBzdHJpbmc7IHR5cGVzOiBzdHJpbmdbXSB9O1xuXHRsZXQgcmVnaXN0cnlUeXBlczogeyBjb250ZW50OiBzdHJpbmc7IHR5cGVzOiBzdHJpbmdbXSB9IHwgdW5kZWZpbmVkO1xuXHRsZXQgb3V0cHV0UGF0aDogc3RyaW5nO1xuXG5cdGlmICh1c2VNb2R1bGVBdWdtZW50YXRpb24pIHtcblx0XHQvLyBMZWdhY3kgbW9kZTogZ2VuZXJhdGUgZ2xvYmFsIGF1Z21lbnRhdGlvbiBmaWxlIChpbmRleC5kLnRzKVxuXHRcdGdlbmVyYXRlZFR5cGVzID0gZ2VuZXJhdG9yLmdlbmVyYXRlR2xvYmFsQXVnbWVudGF0aW9uKCk7XG5cdH0gZWxzZSB7XG5cdFx0Ly8gRGVmYXVsdCBtb2RlOiBnZW5lcmF0ZSB0eXBlcy50cyBmb3IgbWFudWFsIGltcG9ydHNcblx0XHRnZW5lcmF0ZWRUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZVR5cGVzRmlsZSgpO1xuXG5cdFx0Ly8gR2VuZXJhdGUgcmVnaXN0cnkudHMgZm9yIHR5cGUtc2FmZSBsb29rdXAoKSBmdW5jdGlvblxuXHRcdHJlZ2lzdHJ5VHlwZXMgPSBnZW5lcmF0b3IuZ2VuZXJhdGVUeXBlUmVnaXN0cnkoKTtcblx0fVxuXG5cdC8vIEhBUkQgRkFJTCAoZ3JhcGggaWRlbnRpdHkgbGF3KTogc2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIG1uZW1vbmljYVxuXHQvLyBkZWZpbml0aW9ucywgcGx1cyBncmFwaCByZWZlcmVuY2VzIHRoYXQgc3RheSBhbWJpZ3VvdXMgYWZ0ZXJcblx0Ly8gcGF0aC1hd2FyZSByZXNvbHV0aW9uIG9yIHJlc29sdmUgdG8gbm90aGluZy4gUHJpbnQgZXZlcnkgZmFpbHVyZSB3aXRoXG5cdC8vIGFsbCBpdHMgbG9jYXRpb25zIGFuZCB3cml0ZSBOTyAudGFjdGljYSBvdXRwdXQgYXQgYWxsLlxuXHRjb25zdCBmYXRhbEVycm9ycyA9IFsgLi4uYW5hbHl6ZXIuZ2V0UmVzb2x1dGlvbkVycm9ycygpLCAuLi5nZW5lcmF0b3IuZ2V0UmVzb2x1dGlvbkVycm9ycygpIF07XG5cdGlmIChmYXRhbEVycm9ycy5sZW5ndGggPiAwKSB7XG5cdFx0Y29uc3Qgc2VlbiA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdGxldCBwcmludGVkID0gMDtcblx0XHRmb3IgKGNvbnN0IGVycm9yIG9mIGZhdGFsRXJyb3JzKSB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtlcnJvci5tZXNzYWdlfXwke2Vycm9yLmxvY2F0aW9ucy5qb2luKCd8Jyl9YDtcblx0XHRcdGlmIChzZWVuLmhhcyhrZXkpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0c2Vlbi5hZGQoa2V5KTtcblx0XHRcdHByaW50ZWQrKztcblx0XHRcdGNvbnNvbGUuZXJyb3IoYHRhY3RpY2E6ICR7ZXJyb3IubWVzc2FnZX1gKTtcblx0XHRcdGZvciAoY29uc3QgbG9jYXRpb24gb2YgZXJyb3IubG9jYXRpb25zKSB7XG5cdFx0XHRcdGNvbnNvbGUuZXJyb3IoYCAgYXQgJHtsb2NhdGlvbn1gKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc29sZS5lcnJvcihgdGFjdGljYTogYWJvcnRpbmcg4oCUICR7cHJpbnRlZH0gcmVzb2x1dGlvbiBmYWlsdXJlKHMpOyBubyAudGFjdGljYSBvdXRwdXQgd3JpdHRlbmApO1xuXHRcdHJldHVybiAxO1xuXHR9XG5cblx0Ly8gUHJvamVjdCByb290IGFuY2hvcnMgdGhlIHJlbGF0aXZlIHBhdGhzIHRoZSB3cml0ZXIgZW1pdHM6IC50YWN0aWNhXG5cdC8vIG91dHB1dCBtdXN0IHN0YXkgcG9ydGFibGUgd2hlbiB0aGUgY2hlY2tvdXQgbW92ZXMgYmV0d2VlbiBtYWNoaW5lcy5cblx0Ly8gcmVzb2x2ZSgpIGJvdGggc2lkZXMg4oCUIHRzY29uZmlnUGF0aCBpdHNlbGYgbWF5IGJlIHJlbGF0aXZlLlxuXHRjb25zdCBwcm9qZWN0Um9vdCA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKSk7XG5cdGNvbnN0IHdyaXRlciA9IG5ldyBUeXBlc1dyaXRlcihvcHRpb25zLm91dHB1dERpciwgcHJvamVjdFJvb3QpO1xuXG5cdGlmICh1c2VNb2R1bGVBdWdtZW50YXRpb24pIHtcblx0XHQvLyBMZWdhY3kgbW9kZTogd3JpdGUgZ2xvYmFsIGF1Z21lbnRhdGlvbiBmaWxlIChpbmRleC5kLnRzKVxuXHRcdG91dHB1dFBhdGggPSB3cml0ZXIud3JpdGVHbG9iYWxBdWdtZW50YXRpb24oZ2VuZXJhdGVkVHlwZXMpO1xuXHR9IGVsc2Uge1xuXHRcdC8vIERlZmF1bHQgbW9kZTogd3JpdGUgdHlwZXMudHMgZm9yIG1hbnVhbCBpbXBvcnRzXG5cdFx0b3V0cHV0UGF0aCA9IHdyaXRlci53cml0ZVR5cGVzRmlsZShnZW5lcmF0ZWRUeXBlcyk7XG5cblx0XHRjb25zdCByZWdpc3RyeVBhdGggPSB3cml0ZXIud3JpdGVUbygncmVnaXN0cnkudHMnLCByZWdpc3RyeVR5cGVzIS5jb250ZW50KTtcblxuXHRcdC8vIEdlbmVyYXRlIGluZGV4LnRzIHRvIGV4cG9ydCBldmVyeXRoaW5nXG5cdFx0Y29uc3QgaW5kZXhDb250ZW50ID0gYC8vIEdlbmVyYXRlZCBieSBAbW5lbW9uaWNhL3RhY3RpY2EgLSBETyBOT1QgRURJVFxuLy8gRXhwb3J0IGFsbCBnZW5lcmF0ZWQgdHlwZXNcblxuZXhwb3J0ICogZnJvbSAnLi90eXBlcyR7b3B0aW9ucy5lc20gPyAnLmpzJyA6ICcnfSc7XG5leHBvcnQgKiBmcm9tICcuL3JlZ2lzdHJ5JHtvcHRpb25zLmVzbSA/ICcuanMnIDogJyd9JztcbmA7XG5cdFx0d3JpdGVyLndyaXRlVG8oJ2luZGV4LnRzJywgaW5kZXhDb250ZW50KTtcblxuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgcmVnaXN0cnkudHMgYXQ6ICR7cmVnaXN0cnlQYXRofWApO1xuXHRcdH1cblx0fVxuXG5cdC8vIEdlbmVyYXRlIGRlZmluaXRpb25zLmpzb24gYW5kIHVzYWdlcy5qc29uIGZvciBjb2RlIG5hdmlnYXRpb25cblx0Ly8gSW5jbHVkZSBib3RoIG1uZW1vbmljYSBhbmQgdG9wb2xvZ2ljYSBkZWZpbml0aW9uc1xuXHRjb25zdCBkZWZpbml0aW9ucyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0RGVmaW5pdGlvbnMoKSk7XG5cdGNvbnN0IHVzYWdlcyA9IG5ldyBNYXAoYW5hbHl6ZXIuZ2V0VXNhZ2VzKCkpO1xuXHRcblx0Ly8gQWRkIHRvcG9sb2dpY2EgdHlwZXMgdG8gZGVmaW5pdGlvbnNcblx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCB0eXBlTm9kZSBdIG9mIHRvcG9sb2dpY2FUeXBlcykge1xuXHRcdC8vIFNraXAgaWYgYWxyZWFkeSBleGlzdHMgKHByZWZlciBtbmVtb25pY2EncyBhbmFseXNpcylcblx0XHRpZiAoZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXHRcdFxuXHRcdGNvbnN0IGRlZmluaXRpb246IGltcG9ydCgnLi90eXBlcycpLkRlZmluaXRpb25JbmZvID0ge1xuXHRcdFx0bmFtZSAgICAgICAgOiB0eXBlTm9kZS5uYW1lLFxuXHRcdFx0bG9jYXRpb24gICAgOiBgJHt0eXBlTm9kZS5zb3VyY2VGaWxlfToke3R5cGVOb2RlLmxpbmV9OiR7dHlwZU5vZGUuY29sdW1ufWAsXG5cdFx0XHRraW5kICAgICAgICA6ICdkZWZpbmUnLFxuXHRcdFx0cGFyZW50ICAgICAgOiB0eXBlTm9kZS5wYXJlbnQgPyB0eXBlTm9kZS5wYXJlbnQuZnVsbFBhdGggOiBudWxsLFxuXHRcdFx0c3RyaWN0Q2hhaW4gOiB0cnVlLFxuXHRcdFx0YmxvY2tFcnJvcnMgOiBmYWxzZVxuXHRcdH07XG5cdFx0ZGVmaW5pdGlvbnMuc2V0KGZ1bGxQYXRoLCBkZWZpbml0aW9uKTtcblx0fVxuXG5cdC8vIExvY2FsLXNjb3BlIHdhbGsgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgUGhhc2UgMik6IGZ1bmN0aW9uL21ldGhvZC9hcnJvd1xuXHQvLyBzY29wZXMgb25seSAobm8gYmxvY2sgc2NvcGVzIOKAlCBkZWNpc2lvbiA1KSwgdmFyaWFibGVzIHdpdGggaXNNdXRhYmxlIGFuZFxuXHQvLyByZWFzc2lnbm1lbnQgc2l0ZXMgKGRlY2lzaW9uIDYpLiBSdW5zIGFmdGVyIGRlZmluaXRpb25zIGFyZSBrbm93biBzb1xuXHQvLyB2YXJpYWJsZSB0eXBlUGF0aHMgY2FuIHJlc29sdmU7IGhvbGRlclNjb3BlSWQgaXMgYXR0YWNoZWQgdG8gdXNhZ2VzXG5cdC8vIGJlZm9yZSB0aGV5IGFyZSB3cml0dGVuLlxuXHRjb25zdCBzY29wZVdhbGtlciA9IG5ldyBMb2NhbFNjb3BlV2Fsa2VyKCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdHNjb3BlV2Fsa2VyLmFkZEZpbGUoc291cmNlRmlsZSk7XG5cdH1cblx0Y29uc3Qgc2NvcGVSZXNvbHZlcjogU2NvcGVUeXBlUmVzb2x2ZXIgPSB7XG5cdFx0cmVzb2x2ZUJ5TmFtZSA6IChuYW1lOiBzdHJpbmcpOiBzdHJpbmcgfCB1bmRlZmluZWQgPT4ge1xuXHRcdFx0aWYgKGRlZmluaXRpb25zLmhhcyhuYW1lKSkge1xuXHRcdFx0XHRyZXR1cm4gbmFtZTtcblx0XHRcdH1cblx0XHRcdGxldCBmb3VuZDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRcdFx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCBkZWZpbml0aW9uIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRcdFx0aWYgKGRlZmluaXRpb24ubmFtZSAhPT0gbmFtZSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChmb3VuZCkge1xuXHRcdFx0XHRcdC8vIEFtYmlndW91cyBuYW1lIOKAlCBubyB0eXBlIGNoZWNrZXIsIHNvIHJlZnVzZSB0byBndWVzc1xuXHRcdFx0XHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Zm91bmQgPSBmdWxsUGF0aDtcblx0XHRcdH1cblx0XHRcdHJldHVybiBmb3VuZDtcblx0XHR9LFxuXHRcdGhhc1BhdGggOiAoZnVsbFBhdGg6IHN0cmluZyk6IGJvb2xlYW4gPT4ge1xuXHRcdFx0Y29uc3QgcmVzdWx0ID0gZGVmaW5pdGlvbnMuaGFzKGZ1bGxQYXRoKTtcblx0XHRcdHJldHVybiByZXN1bHQ7XG5cdFx0fSxcblx0XHQvLyBUaGUgYW5hbHl6ZXIncyBvd24gbG9va3VwIGxhdywgYWdhaW5zdCB0aGUgc2FtZSBjb21wbGV0ZSBncmFwaCB0aGVcblx0XHQvLyB1c2FnZXMgcGFzcyByZXNvbHZlZCB3aXRoIOKAlCBhIGxvb2t1cCgpIGluaXRpYWxpemVyIHRoZSBhbmFseXplclxuXHRcdC8vIGFjY2VwdGVkIChlLmcuIGFuIGltcG9ydGVkIEhvbGRlci5sb29rdXAoJ1Rva2VuJykpIGxhbmRzIHRoZSBzYW1lXG5cdFx0Ly8gZnVsbFBhdGggaW4gc2NvcGVzLmpzb24gaW5zdGVhZCBvZiBzdGFydmluZyB0aGUgY3JlYXRpb24tZ3JhcGhcblx0XHQvLyBhbmNob3JzLiBSZWplY3RlZCBsb29rdXBzIHN0YXkgdHlwZVBhdGgtbGVzcyBoZXJlOyB0aGUgYW5hbHl6ZXJcblx0XHQvLyBhbHJlYWR5IGhhcmQtZmFpbGVkIHRoZSBydW4gYWJvdmUuXG5cdFx0cmVzb2x2ZUxvb2t1cCA6IChjYWxsOiB0cy5DYWxsRXhwcmVzc2lvbik6IHN0cmluZyB8IHVuZGVmaW5lZCA9PiB7XG5cdFx0XHRjb25zdCByZXNvbHZlZCA9IGFuYWx5emVyLnJlc29sdmVMb29rdXBDYWxsUGF0aChjYWxsKTtcblx0XHRcdHJldHVybiByZXNvbHZlZDtcblx0XHR9LFxuXHR9O1xuXHRjb25zdCBzY29wZUFuYWx5c2lzID0gc2NvcGVXYWxrZXIuYnVpbGQoc2NvcGVSZXNvbHZlcik7XG5cdExvY2FsU2NvcGVXYWxrZXIuYXR0YWNoSG9sZGVyU2NvcGVJZHModXNhZ2VzLCBzY29wZVdhbGtlcik7XG5cblx0Y29uc3QgZGVmaW5pdGlvbnNQYXRoID0gd3JpdGVyLndyaXRlRGVmaW5pdGlvbnNGaWxlKGRlZmluaXRpb25zLCBncmFwaCk7XG5cdGNvbnN0IHVzYWdlc1BhdGggPSB3cml0ZXIud3JpdGVVc2FnZXNGaWxlKHVzYWdlcyk7XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgZGVmaW5pdGlvbnMuanNvbiBhdDogJHtkZWZpbml0aW9uc1BhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCB1c2FnZXMuanNvbiBhdDogJHt1c2FnZXNQYXRofWApO1xuXHR9XG5cblx0Ly8gRGV0ZXJtaW5lIEVEUyBzZXR0aW5nOiBleHBsaWNpdCBmbGFnID4gYXV0by1kZXRlY3QgZGl2ZSA+IGRlZmF1bHQgb2ZmXG5cdGxldCBlbmFibGVFRFMgPSBvcHRpb25zLmVkcztcblx0aWYgKGVuYWJsZUVEUyA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0ZW5hYmxlRURTID0gaGFzRGl2ZURlcGVuZGVuY3kocHJvamVjdERpcik7XG5cdH1cblxuXHRpZiAoZW5hYmxlRURTKSB7XG5cdFx0Y29uc3QgZWRzID0gYW5hbHl6ZXIuZ2V0RURTVXNhZ2VzKCk7XG5cdFx0YXR0YWNoV3JhcEpvaW5EYXRhKGVkcywgc2NvcGVXYWxrZXIsIHNjb3BlQW5hbHlzaXMpO1xuXHRcdGNvbnN0IGVkc1BhdGggPSB3cml0ZXIud3JpdGVFRFNGaWxlKGVkcyk7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBlZHMuanNvbiBhdDogJHtlZHNQYXRofWApO1xuXHRcdH1cblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBmbG93Lmpzb24gKG5hdGl2ZSBpbnN0YW5jZSB1c2FnZSB0cmFja2luZylcblx0Y29uc3QgZmxvdyA9IGFuYWx5emVyLmdldEZsb3dVc2FnZXMoKTtcblx0Y29uc3QgZmxvd1BhdGggPSB3cml0ZXIud3JpdGVGbG93RmlsZShmbG93KTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IGZsb3dDb3VudCA9IEFycmF5LmZyb20oZmxvdy52YWx1ZXMoKSkucmVkdWNlKChzdW0sIGFycikgPT4gc3VtICsgYXJyLmxlbmd0aCwgMCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBmbG93Lmpzb24gYXQ6ICR7Zmxvd1BhdGh9ICgke2Zsb3dDb3VudH0gZmxvdyBlbnRyaWVzKWApO1xuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIG1vZHVsZXMuanNvbiAobW9kdWxlLXNjb3BlIGdyYXBoOiBpbXBvcnRzL2V4cG9ydHMsXG5cdC8vIGRlcGVuZGVuY2llcywgY3ljbGVzLCBjcm9zcy1tb2R1bGUgbW5lbW9uaWNhLXR5cGUgZWRnZXMpXG5cdGNvbnN0IGRlZmluZWRUeXBlc0J5RmlsZSA9IG5ldyBNYXA8c3RyaW5nLCBzdHJpbmdbXT4oKTtcblx0Zm9yIChjb25zdCBbIGZ1bGxQYXRoLCBkZWZpbml0aW9uIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRjb25zdCB7IGxvY2F0aW9uIH0gPSBkZWZpbml0aW9uO1xuXHRcdGNvbnN0IGxhc3RDb2xvbiA9IGxvY2F0aW9uLmxhc3RJbmRleE9mKCc6Jyk7XG5cdFx0Y29uc3QgcHJldkNvbG9uID0gbG9jYXRpb24ubGFzdEluZGV4T2YoJzonLCBsYXN0Q29sb24gLSAxKTtcblx0XHRjb25zdCBmaWxlID0gbG9jYXRpb24uc2xpY2UoMCwgcHJldkNvbG9uKTtcblx0XHRjb25zdCBsaXN0ID0gZGVmaW5lZFR5cGVzQnlGaWxlLmdldChmaWxlKSA/PyBbXTtcblx0XHRsaXN0LnB1c2goZnVsbFBhdGgpO1xuXHRcdGRlZmluZWRUeXBlc0J5RmlsZS5zZXQoZmlsZSwgbGlzdCk7XG5cdH1cblx0Y29uc3QgbW9kdWxlR3JhcGggPSBtb2R1bGVHcmFwaEJ1aWxkZXIuYnVpbGQoZGVmaW5lZFR5cGVzQnlGaWxlKTtcblx0Y29uc3QgbW9kdWxlc1BhdGggPSB3cml0ZXIud3JpdGVNb2R1bGVzRmlsZShtb2R1bGVHcmFwaCk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBtb2R1bGVDb3VudCA9IG1vZHVsZUdyYXBoLm1vZHVsZXMuc2l6ZTtcblx0XHRjb25zdCBlZGdlQ291bnQgPSBtb2R1bGVHcmFwaC5lZGdlcy5sZW5ndGg7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBtb2R1bGVzLmpzb24gYXQ6ICR7bW9kdWxlc1BhdGh9ICgke21vZHVsZUNvdW50fSBtb2R1bGVzLCAke2VkZ2VDb3VudH0gZWRnZXMpYCk7XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgc2NvcGVzLmpzb24gKGxvY2FsLXNjb3BlIHdhbGtlcjogc2NvcGVzLCB2YXJpYWJsZXMsXG5cdC8vIHJlYXNzaWdubWVudCBmbG93LXRlcm1pbmF0aW9uIHBvaW50cylcblx0Y29uc3Qgc2NvcGVzUGF0aCA9IHdyaXRlci53cml0ZVNjb3Blc0ZpbGUoc2NvcGVBbmFseXNpcyk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBzY29wZUNvdW50ID0gc2NvcGVBbmFseXNpcy5zY29wZXMuc2l6ZTtcblx0XHRjb25zdCB2YXJpYWJsZUNvdW50ID0gc2NvcGVBbmFseXNpcy52YXJpYWJsZXMuc2l6ZTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHNjb3Blcy5qc29uIGF0OiAke3Njb3Blc1BhdGh9ICgke3Njb3BlQ291bnR9IHNjb3BlcywgJHt2YXJpYWJsZUNvdW50fSB2YXJpYWJsZXMpYCk7XG5cdH1cblxuXHQvLyBUaGUgaW5zaWRlLW91dCBjcmVhdGlvbiB3YWxrIChpbnN0cnVtZW50YXRpb24gd2Fsa2VyIFBoYXNlIDMpOiBhbmNob3JzXG5cdC8vIGFyZSB0aGUgaW5zdGFudGlhdGlvbiB1c2FnZXM7IGNhbGxlcnMgYXJlIGZvbGxvd2VkIHNhbWUtZmlsZSBhbmRcblx0Ly8gY3Jvc3MtZmlsZSAobW9kdWxlIGdyYXBoLCBiYXJyZWxzIGNoYXNlZCkgdW50aWwgb25seSBzdGFydGVycyByZW1haW4uXG5cdGNvbnN0IHNvdXJjZUZpbGVzQnlQYXRoID0gbmV3IE1hcDxzdHJpbmcsIHRzLlNvdXJjZUZpbGU+KCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdHNvdXJjZUZpbGVzQnlQYXRoLnNldChwYXRoLnJlc29sdmUoc291cmNlRmlsZS5maWxlTmFtZSksIHNvdXJjZUZpbGUpO1xuXHR9XG5cdGNvbnN0IGNyZWF0aW9uR3JhcGhCdWlsZGVyID0gbmV3IENyZWF0aW9uR3JhcGhCdWlsZGVyKG1vZHVsZUdyYXBoLCBzY29wZUFuYWx5c2lzLCBzY29wZVdhbGtlciwgc291cmNlRmlsZXNCeVBhdGgpO1xuXHRjb25zdCBjcmVhdGlvbkdyYXBoID0gY3JlYXRpb25HcmFwaEJ1aWxkZXIuYnVpbGQodXNhZ2VzKTtcblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgaW5zdHJ1bWVudGF0aW9uLmpzb24gKGZyYW1ld29yayBsaWZlY3ljbGUgY3Jvc3Nyb2Fkc1xuXHQvLyBmcm9tIHRoZSBsb2FkZWQgcGx1Z2lucyDigJQgc3ludGFjdGljIGRldGVjdGlvbiBuZWVkcyBubyBkaXZlXG5cdC8vIGRlcGVuZGVuY3ksIHVubGlrZSBlZHMuanNvbikuIHYyIGNhcnJpZXMgdGhlIGNyZWF0aW9uIGdyYXBoXG5cdC8vIGFsb25nc2lkZSB0aGUgcG9pbnRzLlxuXHRjb25zdCBpbnN0cnVtZW50YXRpb24gPSBhbmFseXplci5nZXRJbnN0cnVtZW50YXRpb25Qb2ludHMoKTtcblx0Y29uc3QgaW5zdHJ1bWVudGF0aW9uUGF0aCA9IHdyaXRlci53cml0ZUluc3RydW1lbnRhdGlvbkZpbGUoaW5zdHJ1bWVudGF0aW9uLCBjcmVhdGlvbkdyYXBoKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IG5vZGVDb3VudCA9IGNyZWF0aW9uR3JhcGgubm9kZXMubGVuZ3RoO1xuXHRcdGNvbnN0IGVkZ2VDb3VudCA9IGNyZWF0aW9uR3JhcGguZWRnZXMubGVuZ3RoO1xuXHRcdGNvbnN0IGFuY2hvckNvdW50ID0gY3JlYXRpb25HcmFwaC5hbmNob3JzLmxlbmd0aDtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGluc3RydW1lbnRhdGlvbi5qc29uIGF0OiAke2luc3RydW1lbnRhdGlvblBhdGh9ICgke2luc3RydW1lbnRhdGlvbi5sZW5ndGh9IHBvaW50cylgKTtcblx0XHRjb25zb2xlLmxvZyhgICBjcmVhdGlvbiBncmFwaDogJHtub2RlQ291bnR9IG5vZGVzLCAke2VkZ2VDb3VudH0gZWRnZXMsICR7YW5jaG9yQ291bnR9IGFuY2hvcnNgKTtcblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBjb250cm9sLmpzb24gKGxldGhlIGNvbnRyYWN0LCBmb3JtYXQgMS4xKTogdGhlIHNhbWVcblx0Ly8gY3JlYXRpb24gZ3JhcGggYW5kIHBvaW50cyBhcyBpbnN0cnVtZW50YXRpb24uanNvbiwgcmVuZGVyZWQgdW5kZXIgdGhlXG5cdC8vIGNyb3NzLWxhbmd1YWdlIGBjYWxsZXJzYC9gcG9pbnRzYCBrZXlzLlxuXHRjb25zdCBjb250cm9sUGF0aCA9IHdyaXRlci53cml0ZUNvbnRyb2xGaWxlKGluc3RydW1lbnRhdGlvbiwgY3JlYXRpb25HcmFwaCk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGNvbnRyb2wuanNvbiBhdDogJHtjb250cm9sUGF0aH1gKTtcblx0fVxuXG5cdC8vIEdlbmVyYXRlIGhpZXJhcmNoeS5qc29uIChzdHJ1Y3R1cmVkKSBhbmQgaGllcmFyY2h5LnR4dCAoQVNDSUkgdHJlZSkgZm9yIHRoZSBUcmllXG5cdGNvbnN0IGhpZXJhcmNoeVJvb3RzID0gZ3JhcGgudG9IaWVyYXJjaHkoKTtcblx0Y29uc3QgaGllcmFyY2h5SnNvblBhdGggPSB3cml0ZXIud3JpdGVIaWVyYXJjaHlGaWxlKGhpZXJhcmNoeVJvb3RzKTtcblx0Y29uc3QgaGllcmFyY2h5VGV4dCA9IHJlbmRlclR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHRjb25zdCBoaWVyYXJjaHlUeHRQYXRoID0gd3JpdGVyLndyaXRlVG8oJ2hpZXJhcmNoeS50eHQnLCBoaWVyYXJjaHlUZXh0KTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaGllcmFyY2h5Lmpzb24gYXQ6ICR7aGllcmFyY2h5SnNvblBhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBoaWVyYXJjaHkudHh0IGF0OiAke2hpZXJhcmNoeVR4dFBhdGh9YCk7XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgY29sbGVjdGlvbnMuanNvbiAodGhlIGNvbGxlY3Rpb24gbWFuaWZlc3Q6IGlkcywgZGlzcGxheVxuXHQvLyBuYW1lcywgT3B0aW9uLUIgcmVnaXN0cnkgaW50ZXJmYWNlcywgY2FsbCBzaXRlcyDigJQgdGhlIGlk4oaUaW50ZXJmYWNlIGpvaW5cblx0Ly8ga2V5IGJldHdlZW4gdGhlIHByZWZpeGVkIGdyYXBoIG91dHB1dHMgYW5kIHRoZSB0eXBlcy50cyBhbGlhc2VzKVxuXHRjb25zdCBjb2xsZWN0aW9uc1BhdGggPSB3cml0ZXIud3JpdGVDb2xsZWN0aW9uc0ZpbGUoYW5hbHl6ZXIuZ2V0Q29sbGVjdGlvbnNNYW5pZmVzdCgpKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgY29sbGVjdGlvbnMuanNvbiBhdDogJHtjb2xsZWN0aW9uc1BhdGh9YCk7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCB0eXBlcyBhdDogJHtvdXRwdXRQYXRofWApO1xuXHRcdGNvbnNvbGUubG9nKGBNb2RlOiAke3VzZU1vZHVsZUF1Z21lbnRhdGlvbiA/ICdnbG9iYWwgYXVnbWVudGF0aW9uIChsZWdhY3kpJyA6ICd0eXBlcyBmaWxlIChkZWZhdWx0KSd9YCk7XG5cdFx0Y29uc29sZS5sb2coYEZvdW5kICR7Z2VuZXJhdGVkVHlwZXMudHlwZXMubGVuZ3RofSB0eXBlczpgKTtcblx0XHRwcmludFR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHR9IGVsc2Uge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgJHtnZW5lcmF0ZWRUeXBlcy50eXBlcy5sZW5ndGh9IHR5cGVzIGF0ICR7b3B0aW9ucy5vdXRwdXREaXIgfHwgJy50YWN0aWNhJ31gKTtcblx0XHRpZiAodXNlTW9kdWxlQXVnbWVudGF0aW9uKSB7XG5cdFx0XHRjb25zb2xlLmxvZygnVXNpbmcgZ2xvYmFsIGF1Z21lbnRhdGlvbiBtb2RlIChsZWdhY3ksIHVzZSBkZWZhdWx0IG1vZGUgZm9yIHR5cGVzLnRzIG9ubHkpJyk7XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIDA7XG59XG5cbi8qKlxuICogV2F0Y2ggbW9kZVxuICovXG5mdW5jdGlvbiB3YXRjaCAob3B0aW9uczogQ0xJT3B0aW9ucyk6IHZvaWQge1xuXHRjb25zb2xlLmxvZygnU3RhcnRpbmcgd2F0Y2ggbW9kZS4uLicpO1xuXG5cdC8vIEluaXRpYWwgcnVuXG5cdHJ1bihvcHRpb25zKTtcblxuXHQvLyBTZXQgdXAgZmlsZSB3YXRjaGluZ1xuXHRjb25zdCBjaG9raWRhciA9IHJlcXVpcmUoJ2Nob2tpZGFyJyk7XG5cdGNvbnN0IHRzY29uZmlnUGF0aCA9IGZpbmRUc0NvbmZpZyhvcHRpb25zLnByb2plY3QpO1xuXG5cdGlmICghdHNjb25maWdQYXRoKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6IENvdWxkIG5vdCBmaW5kIHRzY29uZmlnLmpzb24nKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cblxuXHRjb25zdCBwcm9qZWN0RGlyID0gcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCk7XG5cdGNvbnN0IHdhdGNoUGF0aHMgPSBvcHRpb25zLmluY2x1ZGUgfHwgWyAnKiovKi50cycgXTtcblx0Y29uc3QgaWdub3JlUGF0aHMgPSBvcHRpb25zLmV4Y2x1ZGUgfHwgWyAnKiovKi5kLnRzJywgJ25vZGVfbW9kdWxlcy8qKicsICcudGFjdGljYS8qKicgXTtcblxuXHRjb25zdCB3YXRjaGVyID0gY2hva2lkYXIud2F0Y2god2F0Y2hQYXRocywge1xuXHRcdGN3ZCAgICAgICAgOiBwcm9qZWN0RGlyLFxuXHRcdGlnbm9yZWQgICAgOiBpZ25vcmVQYXRocyxcblx0XHRwZXJzaXN0ZW50IDogdHJ1ZSxcblx0fSk7XG5cblx0d2F0Y2hlci5vbignY2hhbmdlJywgKGZpbGVQYXRoOiBzdHJpbmcpID0+IHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgRmlsZSBjaGFuZ2VkOiAke2ZpbGVQYXRofWApO1xuXHRcdH1cblx0XHRydW4ob3B0aW9ucyk7XG5cdH0pO1xuXG5cdHdhdGNoZXIub24oJ2FkZCcsIChmaWxlUGF0aDogc3RyaW5nKSA9PiB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEZpbGUgYWRkZWQ6ICR7ZmlsZVBhdGh9YCk7XG5cdFx0fVxuXHRcdHJ1bihvcHRpb25zKTtcblx0fSk7XG5cblx0Y29uc29sZS5sb2coJ1dhdGNoaW5nIGZvciBjaGFuZ2VzLi4uIChQcmVzcyBDdHJsK0MgdG8gc3RvcCknKTtcbn1cblxuLyoqXG4gKiBNYWluIGVudHJ5IHBvaW50XG4gKi9cbmZ1bmN0aW9uIG1haW4gKCk6IHZvaWQge1xuXHRjb25zdCBhcmdzID0gcHJvY2Vzcy5hcmd2LnNsaWNlKDIpO1xuXHRjb25zdCBvcHRpb25zID0gcGFyc2VBcmdzKGFyZ3MpO1xuXG5cdGlmIChvcHRpb25zLmhlbHApIHtcblx0XHRwcmludEhlbHAoKTtcblx0XHRwcm9jZXNzLmV4aXQoMCk7XG5cdH1cblxuXHR0cnkge1xuXHRcdGlmIChvcHRpb25zLndhdGNoKSB7XG5cdFx0XHR3YXRjaChvcHRpb25zKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Y29uc3QgY29kZSA9IHJ1bihvcHRpb25zKTtcblx0XHRcdGlmIChjb2RlKSB7XG5cdFx0XHRcdHByb2Nlc3MuZXhpdChjb2RlKTtcblx0XHRcdH1cblx0XHR9XG5cdH0gY2F0Y2ggKGVycm9yKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6JywgZXJyb3IgaW5zdGFuY2VvZiBFcnJvciA/IGVycm9yLm1lc3NhZ2UgOiBlcnJvcik7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG59XG5cbi8vIFJ1biBpZiBleGVjdXRlZCBkaXJlY3RseVxuaWYgKHJlcXVpcmUubWFpbiA9PT0gbW9kdWxlKSB7XG5cdG1haW4oKTtcbn1cblxuZXhwb3J0IHtcblx0bWFpbiwgcnVuLCB3YXRjaCwgcGFyc2VBcmdzIFxufTtcbiJdfQ==