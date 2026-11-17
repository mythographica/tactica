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
exports.watchOptions = watchOptions;
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
  tactica                              # Generate types.ts and registry.ts
  tactica --watch                      # Watch mode
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
    // Determine output directories for exclusion
    const outputDirs = generatedOutputDirs(options, tsconfigPath);
    const [outputDirPath, conventionalOutputDir] = outputDirs;
    // a handler importing from either dir names its own generated type
    analyzer.setGeneratedOutputDirs(outputDirs);
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
    // Analyzer errors (e.g. an unnamed lazy() call) never abort the run —
    // the offending call is simply skipped — but they are ALWAYS printed,
    // once each: both passes visit the same call sites, so dedupe by key.
    const analyzerErrors = [];
    for (const sourceFile of sourceFiles) {
        if (options.verbose) {
            console.log(`Analyzing (definitions): ${sourceFile.fileName}`);
        }
        try {
            const definitionsPass = analyzer.analyzeFile(sourceFile);
            analyzerErrors.push(...definitionsPass.errors);
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
            const usagesPass = analyzer.analyzeFile(sourceFile);
            analyzerErrors.push(...usagesPass.errors);
        }
        catch (err) {
            console.error(`Error analyzing ${sourceFile.fileName}:`, err);
            throw err;
        }
    }
    const seenWarnings = new Set();
    for (const analyzerError of analyzerErrors) {
        const key = `${analyzerError.file}:${analyzerError.line}:${analyzerError.column}:${analyzerError.message}`;
        if (seenWarnings.has(key)) {
            continue;
        }
        seenWarnings.add(key);
        const relFile = path.relative(projectDir, analyzerError.file);
        console.warn(`tactica: ${relFile}:${analyzerError.line}:${analyzerError.column} ${analyzerError.message}`);
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
    const generator = new generator_1.TypesGenerator(graph, options.esm, options.outputDir, referenceResolver, analyzer.getBuilderValues());
    // Generate everything into memory FIRST — the hard-fail law below may
    // abort the run, and no .tactica output at all may be written then
    const generatedTypes = generator.generateTypesFile();
    const registryTypes = generator.generateTypeRegistry();
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
    // One run: the files below are written together at commit(), or not
    // at all when only their generatedAt stamps would change
    writer.begin();
    const outputPath = writer.writeTypesFile(generatedTypes);
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
    // Always generate control.json (lethe contract, format 1.2): the same
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
    const written = writer.commit();
    const unchangedNote = written ? '' : ' (unchanged, nothing written)';
    if (options.verbose) {
        console.log(`Generated types at: ${outputPath}${unchangedNote}`);
        console.log('Mode: types file (default)');
        console.log(`Found ${generatedTypes.types.length} types:`);
        printTypeHierarchy(graph);
    }
    else {
        const shownDir = options.outputDir || '.tactica';
        console.log(`Generated ${generatedTypes.types.length} types at ${shownDir}${unchangedNote}`);
    }
    return 0;
}
/**
 * The directories tactica writes, as absolute paths: the --output dir and
 * the project-conventional .tactica dir (next to tsconfig). The conventional
 * one is ALWAYS excluded, even when --output points elsewhere: generated
 * files are never project source. resolve() both sides — tsconfigPath may
 * be relative ('./tsconfig.json') while file names are absolute
 */
function generatedOutputDirs(options, tsconfigPath) {
    const outputDirPath = path.resolve(process.cwd(), options.outputDir || '.tactica');
    const conventionalOutputDir = path.resolve(process.cwd(), path.dirname(tsconfigPath), '.tactica');
    const result = [outputDirPath, conventionalOutputDir];
    return result;
}
/**
 * chokidar options for watch mode. The initial run has already happened,
 * so existing files are not reported as added (ignoreInitial: one full
 * run per existing file otherwise). The directories tactica writes are
 * always ignored, whatever the include/exclude globs say: a written file
 * would trigger another run.
 */
function watchOptions(options, tsconfigPath) {
    const projectDir = path.dirname(tsconfigPath);
    const outputDirs = generatedOutputDirs(options, tsconfigPath);
    const ignorePaths = options.exclude || ['**/*.d.ts', 'node_modules/**', '.tactica/**'];
    // chokidar passes paths joined with cwd; resolve() covers relative ones
    const isGenerated = (filePath) => {
        const absolute = path.resolve(projectDir, filePath);
        const inside = outputDirs.some(dir => absolute === dir || absolute.startsWith(dir + path.sep));
        return inside;
    };
    const result = {
        cwd: projectDir,
        ignored: [...ignorePaths, isGenerated],
        ignoreInitial: true,
        persistent: true,
    };
    return result;
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
    const watchPaths = options.include || ['**/*.ts'];
    const watcher = chokidar.watch(watchPaths, watchOptions(options, tsconfigPath));
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQWkvQlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUFBRSxvQ0FBWTtBQS8rQjFDLHVDQUF5QjtBQUN6QiwyQ0FBNkI7QUFDN0IsbUNBQXVDO0FBQ3ZDLCtDQUFpQztBQUNqQyx5Q0FBK0M7QUFDL0MsK0RBQTJEO0FBQzNELDJDQUVxQjtBQUNyQixxQ0FBdUM7QUFDdkMsaURBQW9EO0FBQ3BELHFEQUF3RDtBQUN4RCxxQ0FFa0I7QUFDbEIsbUNBRWlCO0FBMEJqQjs7R0FFRztBQUNILFNBQVMsU0FBUyxDQUFFLElBQWM7SUFDakMsTUFBTSxPQUFPLEdBQWUsRUFBRSxDQUFDO0lBRS9CLEtBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFLENBQUM7UUFDdEMsTUFBTSxHQUFHLEdBQUcsSUFBSSxDQUFFLENBQUMsQ0FBRSxDQUFDO1FBRXRCLFFBQVEsR0FBRyxFQUFFLENBQUM7WUFDZCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssU0FBUztnQkFDYixPQUFPLENBQUMsS0FBSyxHQUFHLElBQUksQ0FBQztnQkFDckIsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxXQUFXO2dCQUNmLE9BQU8sQ0FBQyxPQUFPLEdBQUcsSUFBSSxDQUFFLEVBQUUsQ0FBQyxDQUFFLENBQUM7Z0JBQzlCLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssVUFBVTtnQkFDZCxPQUFPLENBQUMsU0FBUyxHQUFHLElBQUksQ0FBRSxFQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUNoQyxNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFD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O0lBQ2pCLENBQUM7SUFFRCxJQUFJLENBQUM7UUFDSixJQUFJLE9BQU8sQ0FBQyxLQUFLLEVBQUUsQ0FBQztZQUNuQixLQUFLLENBQUMsT0FBTyxDQUFDLENBQUM7UUFDaEIsQ0FBQzthQUFNLENBQUM7WUFDUCxNQUFNLElBQUksR0FBRyxHQUFHLENBQUMsT0FBTyxDQUFDLENBQUM7WUFDMUIsSUFBSSxJQUFJLEVBQUUsQ0FBQztnQkFDVixPQUFPLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ3BCLENBQUM7UUFDRixDQUFDO0lBQ0YsQ0FBQztJQUFDLE9BQU8sS0FBSyxFQUFFLENBQUM7UUFDaEIsT0FBTyxDQUFDLEtBQUssQ0FBQyxRQUFRLEVBQUUsS0FBSyxZQUFZLEtBQUssQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLE9BQU8sQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDeEUsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQztJQUNqQixDQUFDO0FBQ0YsQ0FBQztBQUVELDJCQUEyQjtBQUMzQixJQUFJLE9BQU8sQ0FBQyxJQUFJLEtBQUssTUFBTSxFQUFFLENBQUM7SUFDN0IsSUFBSSxFQUFFLENBQUM7QUFDUixDQUFDIiwic291cmNlc0NvbnRlbnQiOlsiIyEvdXNyL2Jpbi9lbnYgbm9kZVxuJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBmcyBmcm9tICdmcyc7XG5pbXBvcnQgKiBhcyBwYXRoIGZyb20gJ3BhdGgnO1xuaW1wb3J0IHsgY3JlYXRlUmVxdWlyZSB9IGZyb20gJ21vZHVsZSc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7IE1uZW1vbmljYUFuYWx5emVyIH0gZnJvbSAnLi9hbmFseXplcic7XG5pbXBvcnQgeyBUb3BvbG9naWNhQW5hbHl6ZXIgfSBmcm9tICcuL3RvcG9sb2dpY2EtYW5hbHl6ZXInO1xuaW1wb3J0IHtcblx0VHlwZXNHZW5lcmF0b3IsIEdyYXBoUmVmZXJlbmNlUmVzb2x2ZXIgXG59IGZyb20gJy4vZ2VuZXJhdG9yJztcbmltcG9ydCB7IFR5cGVzV3JpdGVyIH0gZnJvbSAnLi93cml0ZXInO1xuaW1wb3J0IHsgTW9kdWxlR3JhcGhCdWlsZGVyIH0gZnJvbSAnLi9tb2R1bGUtZ3JhcGgnO1xuaW1wb3J0IHsgQ3JlYXRpb25HcmFwaEJ1aWxkZXIgfSBmcm9tICcuL2NyZWF0aW9uLWdyYXBoJztcbmltcG9ydCB7XG5cdExvY2FsU2NvcGVXYWxrZXIsIFNjb3BlVHlwZVJlc29sdmVyXG59IGZyb20gJy4vc2NvcGVzJztcbmltcG9ydCB7XG5cdHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UsIFR5cGVHcmFwaEltcGwgXG59IGZyb20gJy4vZ3JhcGgnO1xuaW1wb3J0IHtcblx0VGFjdGljYUNvbmZpZywgVHlwZU5vZGUsIEVEU0luZm8sIFNjb3BlQW5hbHlzaXMsIEFuYWx5emVFcnJvclxufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7IFRhY3RpY2FQbHVnaW4gfSBmcm9tICcuL3BsdWdpbnMnO1xuXG4vKipcbiAqIENMSSBlbnRyeSBwb2ludCBmb3IgVGFjdGljYVxuICpcbiAqIFJ1bnMgdGhlIGFuYWx5emVyIG92ZXIgYSB0c2NvbmZpZyBwcm9qZWN0IGFuZCB3cml0ZXMgLnRhY3RpY2EvIG91dHB1dFxuICovXG5cbmludGVyZmFjZSBDTElPcHRpb25zIGV4dGVuZHMgVGFjdGljYUNvbmZpZyB7XG5cdHdhdGNoPzogYm9vbGVhbjtcblx0cHJvamVjdD86IHN0cmluZztcblx0aGVscD86IGJvb2xlYW47XG5cdC8qKiBDdXN0b20gdG9wb2xvZ2ljYSBkaXJlY3RvcmllcyB0byBzY2FuICovXG5cdHRvcG9sb2dpY2FEaXJzPzogc3RyaW5nW107XG5cdC8qKiBBZGQgLmpzIGV4dGVuc2lvbnMgdG8gcmVsYXRpdmUgaW1wb3J0cyBmb3IgRVNNIE5vZGVOZXh0IHJlc29sdXRpb24gKi9cblx0ZXNtPzogYm9vbGVhbjtcblx0LyoqIEVuYWJsZSBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHRyYWNraW5nICovXG5cdGVkcz86IGJvb2xlYW47XG5cdC8qKiBQcm9ncmFtbWF0aWMgcGx1Z2luczsgY29uZmlnLWZpbGUgcGx1Z2lucyBhcmUgYXBwZW5kZWQgYWZ0ZXIgdGhlc2UgKi9cblx0cGx1Z2lucz86IFRhY3RpY2FQbHVnaW5bXTtcbn1cblxuLyoqXG4gKiBQYXJzZSBjb21tYW5kIGxpbmUgYXJndW1lbnRzXG4gKi9cbmZ1bmN0aW9uIHBhcnNlQXJncyAoYXJnczogc3RyaW5nW10pOiBDTElPcHRpb25zIHtcblx0Y29uc3Qgb3B0aW9uczogQ0xJT3B0aW9ucyA9IHt9O1xuXG5cdGZvciAobGV0IGkgPSAwOyBpIDwgYXJncy5sZW5ndGg7IGkrKykge1xuXHRcdGNvbnN0IGFyZyA9IGFyZ3NbIGkgXTtcblxuXHRcdHN3aXRjaCAoYXJnKSB7XG5cdFx0Y2FzZSAnLXcnOlxuXHRcdGNhc2UgJy0td2F0Y2gnOlxuXHRcdFx0b3B0aW9ucy53YXRjaCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctcCc6XG5cdFx0Y2FzZSAnLS1wcm9qZWN0Jzpcblx0XHRcdG9wdGlvbnMucHJvamVjdCA9IGFyZ3NbICsraSBdO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLW8nOlxuXHRcdGNhc2UgJy0tb3V0cHV0Jzpcblx0XHRcdG9wdGlvbnMub3V0cHV0RGlyID0gYXJnc1sgKytpIF07XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaSc6XG5cdFx0Y2FzZSAnLS1pbmNsdWRlJzpcblx0XHRcdG9wdGlvbnMuaW5jbHVkZSA9IChvcHRpb25zLmluY2x1ZGUgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1lJzpcblx0XHRjYXNlICctLWV4Y2x1ZGUnOlxuXHRcdFx0b3B0aW9ucy5leGNsdWRlID0gKG9wdGlvbnMuZXhjbHVkZSB8fCBbXSkuY29uY2F0KGFyZ3NbICsraSBdLnNwbGl0KCcsJykpO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXYnOlxuXHRcdGNhc2UgJy0tdmVyYm9zZSc6XG5cdFx0XHRvcHRpb25zLnZlcmJvc2UgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXQnOlxuXHRcdGNhc2UgJy0tdG9wb2xvZ2ljYSc6XG5cdFx0XHRvcHRpb25zLnRvcG9sb2dpY2FEaXJzID0gKG9wdGlvbnMudG9wb2xvZ2ljYURpcnMgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZXNtJzpcblx0XHRcdG9wdGlvbnMuZXNtID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tbm8tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gZmFsc2U7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaCc6XG5cdFx0Y2FzZSAnLS1oZWxwJzpcblx0XHRcdG9wdGlvbnMuaGVscCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gb3B0aW9ucztcbn1cblxuLyoqXG4gKiBQcmludCBoZWxwIG1lc3NhZ2VcbiAqL1xuZnVuY3Rpb24gcHJpbnRIZWxwICgpOiB2b2lkIHtcblx0Y29uc29sZS5sb2coYFxuVGFjdGljYSAtIFR5cGUgZGVmaW5pdGlvbiBnZW5lcmF0b3IgZm9yIE1uZW1vbmljYVxuXG5Vc2FnZTogdGFjdGljYSBbb3B0aW9uc11cblxuT3B0aW9uczpcbiAgLXcsIC0td2F0Y2ggICAgICAgICAgICAgICBXYXRjaCBmb3IgZmlsZSBjaGFuZ2VzIGFuZCByZWdlbmVyYXRlIHR5cGVzXG4gIC1wLCAtLXByb2plY3QgICAgICAgICAgICAgUGF0aCB0byB0c2NvbmZpZy5qc29uIChkZWZhdWx0OiAuL3RzY29uZmlnLmpzb24pXG4gIC1vLCAtLW91dHB1dCAgICAgICAgICAgICAgT3V0cHV0IGRpcmVjdG9yeSBmb3IgZ2VuZXJhdGVkIHR5cGVzIChkZWZhdWx0OiAudGFjdGljYSlcbiAgLWksIC0taW5jbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGluY2x1ZGVcbiAgLWUsIC0tZXhjbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGV4Y2x1ZGVcbiAgLXQsIC0tdG9wb2xvZ2ljYSAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIHRvIHNjYW5cbiAgLS1lc20gICAgICAgICAgICAgICAgICAgICBBZGQgLmpzIGV4dGVuc2lvbnMgdG8gcmVsYXRpdmUgaW1wb3J0cyAoTm9kZU5leHQgRVNNKVxuICAtLWVkcyAgICAgICAgICAgICAgICAgICAgIEVuYWJsZSBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHRyYWNraW5nXG4gIC0tbm8tZWRzICAgICAgICAgICAgICAgICAgRGlzYWJsZSBFRFMgdHJhY2tpbmdcbiAgLXYsIC0tdmVyYm9zZSAgICAgICAgICAgICBFbmFibGUgdmVyYm9zZSBsb2dnaW5nXG4gIC1oLCAtLWhlbHAgICAgICAgICAgICAgICAgU2hvdyB0aGlzIGhlbHAgbWVzc2FnZVxuXG5Db25maWd1cmF0aW9uOlxuICBGcmFtZXdvcmsgaW5zdHJ1bWVudGF0aW9uIHZvY2FidWxhcnkgaXMgc3VwcGxpZWQgYnkgcGx1Z2lucy4gUGxhY2UgYVxuICAudGFjdGljYS5qcyAob3IgdGFjdGljYS5jb25maWcuanMpIG5leHQgdG8geW91ciB0c2NvbmZpZy5qc29uOlxuXG4gICAgICBtb2R1bGUuZXhwb3J0cyA9IHsgcGx1Z2luczogWyAneW91ci1mcmFtZXdvcmstYWRhcHRlci90YWN0aWNhJyBdIH07XG5cbiAgRW50cmllcyBhcmUgbW9kdWxlIHNwZWNpZmllcnMgKHJlcXVpcmVkIHJlbGF0aXZlIHRvIHRoZSBjb25maWcgZmlsZSkgb3JcbiAgaW5saW5lIHBsdWdpbiBvYmplY3RzLiBXaXRob3V0IHBsdWdpbnMsIGluc3RydW1lbnRhdGlvbi5qc29uIHBvaW50cyA9IFtdLlxuXG5FeGFtcGxlczpcbiAgdGFjdGljYSAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICMgR2VuZXJhdGUgdHlwZXMudHMgYW5kIHJlZ2lzdHJ5LnRzXG4gIHRhY3RpY2EgLS13YXRjaCAgICAgICAgICAgICAgICAgICAgICAjIFdhdGNoIG1vZGVcbiAgdGFjdGljYSAtLXByb2plY3QgLi9zcmMvdHNjb25maWcuanNvbiAjIEN1c3RvbSB0c2NvbmZpZyBwYXRoXG4gIHRhY3RpY2EgLS1vdXRwdXQgLi90eXBlcy9tbmVtb25pY2EgICAjIEN1c3RvbSBvdXRwdXQgZGlyZWN0b3J5XG4gIHRhY3RpY2EgLS10b3BvbG9naWNhIC4vc3JjL2FpLXR5cGVzICAjIFNjYW4gc3BlY2lmaWMgdG9wb2xvZ2ljYSBkaXJlY3RvcnlcbmApO1xufVxuXG4vKipcbiAqIEZpbmQgdHNjb25maWcuanNvblxuICovXG5mdW5jdGlvbiBmaW5kVHNDb25maWcgKHByb2plY3RQYXRoPzogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0aWYgKHByb2plY3RQYXRoKSB7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmMocHJvamVjdFBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gcHJvamVjdFBhdGg7XG5cdFx0fVxuXHRcdHRocm93IG5ldyBFcnJvcihgUHJvamVjdCBmaWxlIG5vdCBmb3VuZDogJHtwcm9qZWN0UGF0aH1gKTtcblx0fVxuXG5cdC8vIExvb2sgZm9yIHRzY29uZmlnLmpzb24gaW4gY3VycmVudCBkaXJlY3RvcnkgYW5kIHBhcmVudCBkaXJlY3Rvcmllc1xuXHRsZXQgY3VycmVudERpciA9IHByb2Nlc3MuY3dkKCk7XG5cdHdoaWxlIChjdXJyZW50RGlyICE9PSBwYXRoLmRpcm5hbWUoY3VycmVudERpcikpIHtcblx0XHRjb25zdCB0c2NvbmZpZ1BhdGggPSBwYXRoLmpvaW4oY3VycmVudERpciwgJ3RzY29uZmlnLmpzb24nKTtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyh0c2NvbmZpZ1BhdGgpKSB7XG5cdFx0XHRyZXR1cm4gdHNjb25maWdQYXRoO1xuXHRcdH1cblx0XHRjdXJyZW50RGlyID0gcGF0aC5kaXJuYW1lKGN1cnJlbnREaXIpO1xuXHR9XG5cblx0cmV0dXJuIHVuZGVmaW5lZDtcbn1cblxuLyoqXG4gKiBMb2FkIFR5cGVTY3JpcHQgcHJvZ3JhbSBmcm9tIHRzY29uZmlnXG4gKi9cbmZ1bmN0aW9uIGxvYWRQcm9ncmFtICh0c2NvbmZpZ1BhdGg6IHN0cmluZyk6IHRzLlByb2dyYW0ge1xuXHRjb25zdCBjb25maWdGaWxlID0gdHMucmVhZENvbmZpZ0ZpbGUodHNjb25maWdQYXRoLCB0cy5zeXMucmVhZEZpbGUpO1xuXG5cdGlmIChjb25maWdGaWxlLmVycm9yKSB7XG5cdFx0Y29uc3QgZXJyb3JUZXh0ID0gdHMuZmxhdHRlbkRpYWdub3N0aWNNZXNzYWdlVGV4dChcblx0XHRcdGNvbmZpZ0ZpbGUuZXJyb3IubWVzc2FnZVRleHQsXG5cdFx0XHQnXFxuJ1xuXHRcdCk7XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBFcnJvciByZWFkaW5nIHRzY29uZmlnOiAke2Vycm9yVGV4dH1gKTtcblx0fVxuXG5cdC8vIFRhY3RpY2EgYW5hbHl6ZXMgd2l0aCBpdHMgb3duIGJ1bmRsZWQgVHlwZVNjcmlwdCwgd2hpY2ggbWF5IGJlIG5ld2VyXG5cdC8vIHRoYW4gdGhlIGNvbXBpbGVyIHRoZSB1c2VyJ3MgdHNjb25maWcgd2FzIHdyaXR0ZW4gZm9yIChlLmcuIGEgVFM1LWVyYVxuXHQvLyBjb25maWcgY2FycnlpbmcgYGJhc2VVcmxgLCBkZXByZWNhdGVkLWVycm9yZWQgYnkgVFM2J3MgVFM1MTAxKS5cblx0Ly8gQW5hbHlzaXMgbmV2ZXIgZW1pdHMgdXNlciBjb2RlLCBzbyBkZXByZWNhdGlvbiBlcnJvcnMgYXJlIGFib3V0IHRoZVxuXHQvLyB1c2VyJ3MgYnVpbGQgcGlwZWxpbmUsIG5vdCBhYm91dCBhbmFseXphYmlsaXR5IOKAlCBzaWxlbmNlIHRoZW0gZm9yIHRoZVxuXHQvLyBhbmFseXNpcyBwcm9ncmFtLiBVbmNvbmRpdGlvbmFsOiBhIHVzZXItcGlubmVkIG9sZGVyIHZhbHVlICgnNS4wJylcblx0Ly8gZG9lcyBub3Qgc2lsZW5jZSA2LjAgZGVwcmVjYXRpb25zIGFuZCB3b3VsZCBzdGlsbCBmYXRhbCBiZWxvdy5cblx0Y29uc3QgcmF3Q29uZmlnID0gY29uZmlnRmlsZS5jb25maWcgPz8ge307XG5cdHJhd0NvbmZpZy5jb21waWxlck9wdGlvbnMgPSB7XG5cdFx0Li4ucmF3Q29uZmlnLmNvbXBpbGVyT3B0aW9ucyxcblx0XHRpZ25vcmVEZXByZWNhdGlvbnMgOiAnNi4wJyxcblx0fTtcblxuXHRjb25zdCBwYXJzZWRDb25maWcgPSB0cy5wYXJzZUpzb25Db25maWdGaWxlQ29udGVudChcblx0XHRyYXdDb25maWcsXG5cdFx0dHMuc3lzLFxuXHRcdHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpXG5cdCk7XG5cblx0aWYgKHBhcnNlZENvbmZpZy5lcnJvcnMubGVuZ3RoID4gMCkge1xuXHRcdGNvbnN0IGVycm9yTWVzc2FnZXMgPSBwYXJzZWRDb25maWcuZXJyb3JzLm1hcChlID0+XG5cdFx0XHR0cy5mbGF0dGVuRGlhZ25vc3RpY01lc3NhZ2VUZXh0KGUubWVzc2FnZVRleHQsICdcXG4nKSk7XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBFcnJvciBwYXJzaW5nIHRzY29uZmlnOiAke2Vycm9yTWVzc2FnZXMuam9pbignXFxuJyl9YCk7XG5cdH1cblxuXHRjb25zdCBwcm9ncmFtID0gdHMuY3JlYXRlUHJvZ3JhbSh7XG5cdFx0cm9vdE5hbWVzIDogcGFyc2VkQ29uZmlnLmZpbGVOYW1lcyxcblx0XHRvcHRpb25zICAgOiBwYXJzZWRDb25maWcub3B0aW9ucyxcblx0fSk7XG5cblx0cmV0dXJuIHByb2dyYW07XG59XG5cbi8qKlxuICogTG9vayB1cCBhIHZhcmlhYmxlIGJ5IG5hbWUgc3RhcnRpbmcgZnJvbSBhIHNjb3BlLCB3YWxraW5nIG91dHdhcmQgdGhyb3VnaFxuICogcGFyZW50U2NvcGVJZC4gVGhlIGlubmVybW9zdCBiaW5kaW5nIHdpbnMgZXZlbiB3aGVuIGl0IGNhcnJpZXMgbm8gdHlwZVBhdGhcbiAqIChzaGFkb3dpbmcgaG9uZXN0eSDigJQgYW4gdW50eXBlZCBsb2NhbCBzaGFkb3dzIGEgdHlwZWQgb3V0ZXIgb25lKS5cbiAqL1xuZnVuY3Rpb24gcmVzb2x2ZVNjb3BlZFZhcmlhYmxlVHlwZVBhdGggKFxuXHRuYW1lOiBzdHJpbmcsXG5cdHNjb3BlSWQ6IHN0cmluZyxcblx0c2NvcGVBbmFseXNpczogU2NvcGVBbmFseXNpc1xuKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0bGV0IGN1cnJlbnQ6IHN0cmluZyB8IHVuZGVmaW5lZCA9IHNjb3BlSWQ7XG5cdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0Y29uc3QgdmFyaWFibGUgPSBzY29wZUFuYWx5c2lzLnZhcmlhYmxlcy5nZXQoYCR7Y3VycmVudH0jJHtuYW1lfWApO1xuXHRcdGlmICh2YXJpYWJsZSkge1xuXHRcdFx0Y29uc3QgeyB0eXBlUGF0aCB9ID0gdmFyaWFibGU7XG5cdFx0XHRyZXR1cm4gdHlwZVBhdGg7XG5cdFx0fVxuXHRcdGN1cnJlbnQgPSBzY29wZUFuYWx5c2lzLnNjb3Blcy5nZXQoY3VycmVudCk/LnBhcmVudFNjb3BlSWQ7XG5cdH1cblx0cmV0dXJuIHVuZGVmaW5lZDtcbn1cblxuLyoqXG4gKiBKb2luIGRhdGEgZm9yIG1uZW1vZ3JhcGhpY2EncyB3cmFwcGVycyBsYXllcjogcGluIGVhY2ggd3JhcCBlbnRyeSB0byB0aGVcbiAqIHNjb3BlIGhvbGRpbmcgaXRzIGNhbGwgc2l0ZSwgYW5kIHJlc29sdmUgdGhlIHdyYXBwZWQgaW5zdGFuY2UgYXJndW1lbnQnc1xuICogbW5lbW9uaWNhIHR5cGUgdGhyb3VnaCB0aGUgc2NvcGUtdmFyaWFibGUgY2hhaW4uXG4gKi9cbmZ1bmN0aW9uIGF0dGFjaFdyYXBKb2luRGF0YSAoXG5cdGVkczogTWFwPHN0cmluZywgRURTSW5mb1tdPixcblx0c2NvcGVXYWxrZXI6IExvY2FsU2NvcGVXYWxrZXIsXG5cdHNjb3BlQW5hbHlzaXM6IFNjb3BlQW5hbHlzaXNcbik6IHZvaWQge1xuXHRmb3IgKGNvbnN0IGVudHJpZXMgb2YgZWRzLnZhbHVlcygpKSB7XG5cdFx0Zm9yIChjb25zdCBlbnRyeSBvZiBlbnRyaWVzKSB7XG5cdFx0XHRpZiAoZW50cnkua2luZCAhPT0gJ3dyYXAnKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgaG9sZGVyU2NvcGVJZCA9IHNjb3BlV2Fsa2VyLmZpbmRIb2xkZXJTY29wZUlkKGVudHJ5LmxvY2F0aW9uKTtcblx0XHRcdGlmICghaG9sZGVyU2NvcGVJZCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGVudHJ5LnNjb3BlSWQgPSBob2xkZXJTY29wZUlkO1xuXHRcdFx0aWYgKCFlbnRyeS5pbnN0YW5jZUFyZykge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHdyYXBzVHlwZVBhdGggPSByZXNvbHZlU2NvcGVkVmFyaWFibGVUeXBlUGF0aChcblx0XHRcdFx0ZW50cnkuaW5zdGFuY2VBcmcsXG5cdFx0XHRcdGhvbGRlclNjb3BlSWQsXG5cdFx0XHRcdHNjb3BlQW5hbHlzaXNcblx0XHRcdCk7XG5cdFx0XHRpZiAod3JhcHNUeXBlUGF0aCkge1xuXHRcdFx0XHRlbnRyeS53cmFwc1R5cGVQYXRoID0gd3JhcHNUeXBlUGF0aDtcblx0XHRcdH1cblx0XHR9XG5cdH1cbn1cblxuLyoqXG4gKiBSZW5kZXIgdHlwZSBoaWVyYXJjaHkgYXMgYW4gQVNDSUkgdHJlZSBzdHJpbmcuXG4gKiBEaXNwbGF5LW9ubHk6IHNpYmxpbmdzIGFyZSBzb3J0ZWQgYnkgZnVsbFBhdGggYXQgcmVuZGVyIHRpbWUgKGNvZGUtdW5pdFxuICogb3JkZXIg4oCUIGRlZmF1bHQtY29sbGVjdGlvbiBQYXNjYWxDYXNlIHJvb3RzIGxhbmQgYmVmb3JlIHRoZVxuICogYGNvbGxlY3Rpb25fTjo6YC1wcmVmaXhlZCBvbmVzKS4gVGhlIGdyYXBoIGl0c2VsZiBrZWVwcyBkaXNjb3Zlcnkgb3JkZXI7XG4gKiBoaWVyYXJjaHkuanNvbiBpcyB1bmFmZmVjdGVkLlxuICovXG5mdW5jdGlvbiByZW5kZXJUeXBlSGllcmFyY2h5IChncmFwaDogVHlwZUdyYXBoSW1wbCk6IHN0cmluZyB7XG5cdGNvbnN0IGxpbmVzOiBzdHJpbmdbXSA9IFsgJ1R5cGUgSGllcmFyY2h5IChUcmllKTonIF07XG5cblx0ZnVuY3Rpb24gc29ydGVkQnlGdWxsUGF0aCAobm9kZXM6IFR5cGVOb2RlW10pOiBUeXBlTm9kZVtdIHtcblx0XHRjb25zdCBzb3J0ZWQgPSBBcnJheS5mcm9tKG5vZGVzKTtcblx0XHRzb3J0ZWQuc29ydCgoYSwgYikgPT4ge1xuXHRcdFx0aWYgKGEuZnVsbFBhdGggPCBiLmZ1bGxQYXRoKSB7IHJldHVybiAtMTsgfVxuXHRcdFx0aWYgKGEuZnVsbFBhdGggPiBiLmZ1bGxQYXRoKSB7IHJldHVybiAxOyB9XG5cdFx0XHRyZXR1cm4gMDtcblx0XHR9KTtcblx0XHRyZXR1cm4gc29ydGVkO1xuXHR9XG5cblx0ZnVuY3Rpb24gcmVuZGVyTm9kZSAobm9kZTogVHlwZU5vZGUsIHByZWZpeCA9ICcnLCBpc0xhc3QgPSB0cnVlKTogdm9pZCB7XG5cdFx0Y29uc3QgY29ubmVjdG9yID0gaXNMYXN0ID8gJ+KUlOKUgOKUgCAnIDogJ+KUnOKUgOKUgCAnO1xuXHRcdC8vIFVzZSBub2RlLmZ1bGxQYXRoIGRpcmVjdGx5IGFuZCBjb252ZXJ0IGRvdHMgdG8gdW5kZXJzY29yZXNcblx0XHRjb25zdCBpbnN0YW5jZU5hbWUgPSBub2RlLmZ1bGxQYXRoLnJlcGxhY2UoL1xcLi9nLCAnXycpO1xuXHRcdGxpbmVzLnB1c2goYCR7cHJlZml4fSR7Y29ubmVjdG9yfSR7aW5zdGFuY2VOYW1lfWApO1xuXG5cdFx0Y29uc3QgY2hpbGRyZW4gPSBzb3J0ZWRCeUZ1bGxQYXRoKEFycmF5LmZyb20obm9kZS5jaGlsZHJlbi52YWx1ZXMoKSkpO1xuXHRcdGNvbnN0IG5ld1ByZWZpeCA9IHByZWZpeCArIChpc0xhc3QgPyAnICAgICcgOiAn4pSCICAgJyk7XG5cblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IGNoaWxkcmVuLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRyZW5kZXJOb2RlKGNoaWxkcmVuWyBpIF0sIG5ld1ByZWZpeCwgaSA9PT0gY2hpbGRyZW4ubGVuZ3RoIC0gMSk7XG5cdFx0fVxuXHR9XG5cblx0Y29uc3Qgcm9vdHMgPSBzb3J0ZWRCeUZ1bGxQYXRoKEFycmF5LmZyb20oZ3JhcGgucm9vdHMudmFsdWVzKCkpKTtcblx0Zm9yIChsZXQgaSA9IDA7IGkgPCByb290cy5sZW5ndGg7IGkrKykge1xuXHRcdHJlbmRlck5vZGUocm9vdHNbIGkgXSwgJycsIGkgPT09IHJvb3RzLmxlbmd0aCAtIDEpO1xuXHR9XG5cdC8vIEVtcHR5IGxpbmUgYXQgZW5kXG5cdGxpbmVzLnB1c2goJycpO1xuXG5cdGNvbnN0IHJlc3VsdCA9IGxpbmVzLmpvaW4oJ1xcbicpO1xuXHRyZXR1cm4gcmVzdWx0O1xufVxuXG4vKipcbiAqIFByaW50IHR5cGUgaGllcmFyY2h5IHRvIHRoZSBjb25zb2xlLlxuICovXG5mdW5jdGlvbiBwcmludFR5cGVIaWVyYXJjaHkgKGdyYXBoOiBUeXBlR3JhcGhJbXBsKTogdm9pZCB7XG5cdGNvbnN0IG91dHB1dCA9IHJlbmRlclR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHRjb25zb2xlLmxvZyhvdXRwdXQpO1xufVxuXG4vKipcbiAqIENoZWNrIGlmIEBtbmVtb25pY2EvZGl2ZSBpcyBwcmVzZW50IGluIHBhY2thZ2UuanNvbiBkZXBlbmRlbmNpZXNcbiAqL1xuZnVuY3Rpb24gaGFzRGl2ZURlcGVuZGVuY3kgKHByb2plY3REaXI6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRjb25zdCBwYWNrYWdlSnNvblBhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgJ3BhY2thZ2UuanNvbicpO1xuXHRpZiAoIWZzLmV4aXN0c1N5bmMocGFja2FnZUpzb25QYXRoKSkge1xuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXHR0cnkge1xuXHRcdGNvbnN0IGNvbnRlbnQgPSBmcy5yZWFkRmlsZVN5bmMocGFja2FnZUpzb25QYXRoLCAndXRmLTgnKTtcblx0XHRjb25zdCBwa2cgPSBKU09OLnBhcnNlKGNvbnRlbnQpO1xuXHRcdGNvbnN0IGRlcHMgPSBwa2cuZGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdGNvbnN0IGRldkRlcHMgPSBwa2cuZGV2RGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdGNvbnN0IHBlZXJEZXBzID0gcGtnLnBlZXJEZXBlbmRlbmNpZXMgfHwge307XG5cdFx0cmV0dXJuICdAbW5lbW9uaWNhL2RpdmUnIGluIGRlcHMgfHwgJ0BtbmVtb25pY2EvZGl2ZScgaW4gZGV2RGVwcyB8fCAnQG1uZW1vbmljYS9kaXZlJyBpbiBwZWVyRGVwcztcblx0fSBjYXRjaCB7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG59XG5cbi8qKlxuICogU2NhbiBmb3IgdG9wb2xvZ2ljYSBkaXJlY3Rvcnkgc3RydWN0dXJlc1xuICovXG5mdW5jdGlvbiBzY2FuVG9wb2xvZ2ljYURpcmVjdG9yaWVzIChwcm9qZWN0RGlyOiBzdHJpbmcsIGN1c3RvbURpcnM/OiBzdHJpbmdbXSk6IHN0cmluZ1tdIHtcblx0Y29uc3QgZGlyczogc3RyaW5nW10gPSBbXTtcblxuXHQvLyBGaXJzdCwgYWRkIGN1c3RvbSBkaXJlY3RvcmllcyBpZiBzcGVjaWZpZWRcblx0aWYgKGN1c3RvbURpcnMpIHtcblx0XHRmb3IgKGNvbnN0IGRpciBvZiBjdXN0b21EaXJzKSB7XG5cdFx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5pc0Fic29sdXRlKGRpcikgPyBkaXIgOiBwYXRoLmpvaW4ocHJvamVjdERpciwgZGlyKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc29sZS53YXJuKGBXYXJuaW5nOiBUb3BvbG9naWNhIGRpcmVjdG9yeSBub3QgZm91bmQ6ICR7ZGlyUGF0aH1gKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvLyBUaGVuIGF1dG8tZGlzY292ZXIgc3RhbmRhcmQgdG9wb2xvZ2ljYSBkaXJlY3Rvcmllc1xuXHRjb25zdCBwb3NzaWJsZURpcnMgPSBbICdhaS10eXBlcycsICd0eXBlcycsICd0b3BvbG9naWNhLXR5cGVzJyBdO1xuXG5cdGZvciAoY29uc3QgZGlyTmFtZSBvZiBwb3NzaWJsZURpcnMpIHtcblx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsIGRpck5hbWUpO1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdC8vIEF2b2lkIGR1cGxpY2F0ZXNcblx0XHRcdGlmICghZGlycy5pbmNsdWRlcyhkaXJQYXRoKSkge1xuXHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWxzbyBzY2FuIHNyYy8gc3ViZGlyZWN0b3J5XG5cdGNvbnN0IHNyY1BhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgJ3NyYycpO1xuXHRpZiAoZnMuZXhpc3RzU3luYyhzcmNQYXRoKSAmJiBmcy5zdGF0U3luYyhzcmNQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0Zm9yIChjb25zdCBkaXJOYW1lIG9mIHBvc3NpYmxlRGlycykge1xuXHRcdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguam9pbihzcmNQYXRoLCBkaXJOYW1lKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdFx0Ly8gQXZvaWQgZHVwbGljYXRlc1xuXHRcdFx0XHRpZiAoIWRpcnMuaW5jbHVkZXMoZGlyUGF0aCkpIHtcblx0XHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gZGlycztcbn1cblxuLyoqXG4gKiBDb25maWcgZmlsZSBjYW5kaWRhdGVzIChlc2xpbnQtc3R5bGUgcHJvamVjdCBjb25maWcpLCBzZWFyY2hlZCBuZXh0IHRvXG4gKiB0aGUgcmVzb2x2ZWQgdHNjb25maWcgZmlyc3QsIHRoZW4gaW4gdGhlIGN1cnJlbnQgd29ya2luZyBkaXJlY3RvcnkuXG4gKi9cbmNvbnN0IENPTkZJR19GSUxFX05BTUVTID0gWyAnLnRhY3RpY2EuanMnLCAndGFjdGljYS5jb25maWcuanMnIF07XG5cbmludGVyZmFjZSBUYWN0aWNhQ29uZmlnRmlsZSB7XG5cdHBsdWdpbnM/OiBBcnJheTxUYWN0aWNhUGx1Z2luIHwgc3RyaW5nPjtcbn1cblxuLyoqXG4gKiBMb2FkIGZyYW1ld29yay12b2NhYnVsYXJ5IHBsdWdpbnM6IHByb2dyYW1tYXRpYyBvcHRpb25zIGZpcnN0LCB0aGVuIHRoZVxuICogcHJvamVjdCBjb25maWcgZmlsZS4gU3RyaW5nIGVudHJpZXMgYXJlIG1vZHVsZSBzcGVjaWZpZXJzIHJlcXVpcmVkXG4gKiByZWxhdGl2ZSB0byB0aGUgY29uZmlnIGZpbGUgKGUuZy4gYW4gYWRhcHRlciBwYWNrYWdlJ3MgcGx1Z2luIHN1YnBhdGgpLlxuICogV2l0aG91dCBhIGNvbmZpZyBmaWxlIGFuZCB3aXRob3V0IHByb2dyYW1tYXRpYyBwbHVnaW5zIHRoZSBhbmFseXplclxuICogc3RheXMgZnJhbWV3b3JrLWJsaW5kIGFuZCBpbnN0cnVtZW50YXRpb24uanNvbiBjYXJyaWVzIGVtcHR5IHBvaW50cy5cbiAqL1xuZnVuY3Rpb24gbG9hZFRhY3RpY2FQbHVnaW5zIChwcm9qZWN0RGlyOiBzdHJpbmcsIG9wdGlvbnM6IENMSU9wdGlvbnMpOiBUYWN0aWNhUGx1Z2luW10ge1xuXHRjb25zdCBwbHVnaW5zOiBUYWN0aWNhUGx1Z2luW10gPSBbIC4uLihvcHRpb25zLnBsdWdpbnMgfHwgW10pIF07XG5cblx0Y29uc3Qgc2VhcmNoRGlycyA9IFsgcHJvamVjdERpciBdO1xuXHRjb25zdCBjd2QgPSBwcm9jZXNzLmN3ZCgpO1xuXHRpZiAoY3dkICE9PSBwcm9qZWN0RGlyKSB7XG5cdFx0c2VhcmNoRGlycy5wdXNoKGN3ZCk7XG5cdH1cblxuXHRsZXQgY29uZmlnUGF0aDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRmb3IgKGNvbnN0IGRpciBvZiBzZWFyY2hEaXJzKSB7XG5cdFx0Zm9yIChjb25zdCBuYW1lIG9mIENPTkZJR19GSUxFX05BTUVTKSB7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGUgPSBwYXRoLmpvaW4oZGlyLCBuYW1lKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGNhbmRpZGF0ZSkpIHtcblx0XHRcdFx0Y29uZmlnUGF0aCA9IGNhbmRpZGF0ZTtcblx0XHRcdFx0YnJlYWs7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChjb25maWdQYXRoKSB7XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdH1cblxuXHRpZiAoIWNvbmZpZ1BhdGgpIHtcblx0XHRyZXR1cm4gcGx1Z2lucztcblx0fVxuXG5cdC8vIGNyZWF0ZVJlcXVpcmUgYW5jaG9yZWQgYXQgdGhlIGNvbmZpZyBmaWxlOiB0aGUgY29uZmlnJ3Mgb3duIGltcG9ydHNcblx0Ly8gYW5kIHN0cmluZyBwbHVnaW4gc3BlY2lmaWVycyByZXNvbHZlIGFnYWluc3QgdGhlIHByb2plY3QncyBtb2R1bGVzXG5cdGNvbnN0IGNvbmZpZ1JlcXVpcmUgPSBjcmVhdGVSZXF1aXJlKGNvbmZpZ1BhdGgpO1xuXHRjb25zdCBsb2FkZWQgPSBjb25maWdSZXF1aXJlKGNvbmZpZ1BhdGgpO1xuXHRjb25zdCBjb25maWc6IFRhY3RpY2FDb25maWdGaWxlID0gbG9hZGVkICYmIHR5cGVvZiBsb2FkZWQgPT09ICdvYmplY3QnICYmICdkZWZhdWx0JyBpbiBsb2FkZWRcblx0XHQ/IGxvYWRlZC5kZWZhdWx0XG5cdFx0OiBsb2FkZWQ7XG5cdGNvbnN0IGVudHJpZXMgPSBjb25maWcgJiYgQXJyYXkuaXNBcnJheShjb25maWcucGx1Z2lucykgPyBjb25maWcucGx1Z2lucyA6IFtdO1xuXG5cdGZvciAoY29uc3QgZW50cnkgb2YgZW50cmllcykge1xuXHRcdGlmICh0eXBlb2YgZW50cnkgIT09ICdzdHJpbmcnKSB7XG5cdFx0XHRwbHVnaW5zLnB1c2goZW50cnkpO1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXHRcdGNvbnN0IG1vZCA9IGNvbmZpZ1JlcXVpcmUoZW50cnkpO1xuXHRcdGNvbnN0IHBsdWdpbjogVGFjdGljYVBsdWdpbiA9IG1vZCAmJiB0eXBlb2YgbW9kID09PSAnb2JqZWN0JyAmJiAnZGVmYXVsdCcgaW4gbW9kXG5cdFx0XHQ/IG1vZC5kZWZhdWx0XG5cdFx0XHQ6IG1vZDtcblx0XHRwbHVnaW5zLnB1c2gocGx1Z2luKTtcblx0fVxuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBuYW1lcyA9IHBsdWdpbnMubWFwKHBsdWdpbiA9PiBwbHVnaW4ubmFtZSB8fCAnKHVubmFtZWQpJykuam9pbignLCAnKTtcblx0XHRjb25zb2xlLmxvZyhgTG9hZGVkIHRhY3RpY2EgY29uZmlnOiAke2NvbmZpZ1BhdGh9IChwbHVnaW5zOiAke25hbWVzIHx8ICdub25lJ30pYCk7XG5cdH1cblxuXHRyZXR1cm4gcGx1Z2lucztcbn1cblxuLyoqXG4gKiBSdW4gdHlwZSBnZW5lcmF0aW9uLiBSZXR1cm5zIDAgb24gc3VjY2VzczsgMSB3aGVuIHRoZSBncmFwaCBpZGVudGl0eSBsYXdcbiAqIGFib3J0ZWQgdGhlIHJ1biAoZmFpbHVyZXMgcHJpbnRlZCwgbm8gLnRhY3RpY2Egb3V0cHV0IHdyaXR0ZW4pLlxuICovXG5mdW5jdGlvbiBydW4gKG9wdGlvbnM6IENMSU9wdGlvbnMpOiBudW1iZXIge1xuXHRjb25zdCB0c2NvbmZpZ1BhdGggPSBmaW5kVHNDb25maWcob3B0aW9ucy5wcm9qZWN0KTtcblxuXHRpZiAoIXRzY29uZmlnUGF0aCkge1xuXHRcdGNvbnNvbGUuZXJyb3IoJ0Vycm9yOiBDb3VsZCBub3QgZmluZCB0c2NvbmZpZy5qc29uJyk7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBVc2luZyB0c2NvbmZpZzogJHt0c2NvbmZpZ1BhdGh9YCk7XG5cdH1cblxuXHQvLyBGcmFtZXdvcmsgdm9jYWJ1bGFyeSBhcnJpdmVzIHZpYSBwbHVnaW5zIOKAlCBhIGNvbmZpZyBmaWxlIG5leHQgdG8gdGhlXG5cdC8vIHRzY29uZmlnIChvciBpbiBjd2QpIGFuZC9vciBwcm9ncmFtbWF0aWMgb3B0aW9ucy4gTm9uZSBsb2FkZWQgbWVhbnNcblx0Ly8gdGhlIGFuYWx5emVyIGRldGVjdHMgemVybyBpbnN0cnVtZW50YXRpb24gcG9pbnRzLlxuXHRjb25zdCBwbHVnaW5zID0gbG9hZFRhY3RpY2FQbHVnaW5zKHBhdGguZGlybmFtZShwYXRoLnJlc29sdmUodHNjb25maWdQYXRoKSksIG9wdGlvbnMpO1xuXG5cdC8vIExvYWQgVHlwZVNjcmlwdCBwcm9ncmFtXG5cdGNvbnN0IHByb2dyYW0gPSBsb2FkUHJvZ3JhbSh0c2NvbmZpZ1BhdGgpO1xuXG5cdC8vIENyZWF0ZSBhbmFseXplclxuXHRjb25zdCBhbmFseXplciA9IG5ldyBNbmVtb25pY2FBbmFseXplcihwcm9ncmFtLCBwbHVnaW5zKTtcblxuXHQvLyBEZXRlcm1pbmUgb3V0cHV0IGRpcmVjdG9yaWVzIGZvciBleGNsdXNpb25cblx0Y29uc3Qgb3V0cHV0RGlycyA9IGdlbmVyYXRlZE91dHB1dERpcnMob3B0aW9ucywgdHNjb25maWdQYXRoKTtcblx0Y29uc3QgWyBvdXRwdXREaXJQYXRoLCBjb252ZW50aW9uYWxPdXRwdXREaXIgXSA9IG91dHB1dERpcnM7XG5cdC8vIGEgaGFuZGxlciBpbXBvcnRpbmcgZnJvbSBlaXRoZXIgZGlyIG5hbWVzIGl0cyBvd24gZ2VuZXJhdGVkIHR5cGVcblx0YW5hbHl6ZXIuc2V0R2VuZXJhdGVkT3V0cHV0RGlycyhvdXRwdXREaXJzKTtcblxuXHQvLyBDb2xsZWN0IHNvdXJjZSBmaWxlcyB0byBhbmFseXplXG5cdGNvbnN0IHNvdXJjZUZpbGVzOiB0cy5Tb3VyY2VGaWxlW10gPSBbXTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHByb2dyYW0uZ2V0U291cmNlRmlsZXMoKSkge1xuXHRcdGlmIChzb3VyY2VGaWxlLmlzRGVjbGFyYXRpb25GaWxlKSB7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cblx0XHRjb25zdCBhYnNvbHV0ZUZpbGVOYW1lID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdGlmIChhYnNvbHV0ZUZpbGVOYW1lLnN0YXJ0c1dpdGgob3V0cHV0RGlyUGF0aCArIHBhdGguc2VwKSB8fFxuXHRcdFx0YWJzb2x1dGVGaWxlTmFtZS5zdGFydHNXaXRoKGNvbnZlbnRpb25hbE91dHB1dERpciArIHBhdGguc2VwKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZXhjbHVkZSBwYXR0ZXJuc1xuXHRcdGlmIChvcHRpb25zLmV4Y2x1ZGUpIHtcblx0XHRcdGNvbnN0IHNob3VsZEV4Y2x1ZGUgPSBvcHRpb25zLmV4Y2x1ZGUuc29tZShwYXR0ZXJuID0+XG5cdFx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUuaW5jbHVkZXMocGF0dGVybi5yZXBsYWNlKC9cXCovZywgJycpKSk7XG5cdFx0XHRpZiAoc2hvdWxkRXhjbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBDaGVjayBpbmNsdWRlIHBhdHRlcm5zXG5cdFx0aWYgKG9wdGlvbnMuaW5jbHVkZSAmJiBvcHRpb25zLmluY2x1ZGUubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3Qgc2hvdWxkSW5jbHVkZSA9IG9wdGlvbnMuaW5jbHVkZS5zb21lKHBhdHRlcm4gPT5cblx0XHRcdFx0c291cmNlRmlsZS5maWxlTmFtZS5pbmNsdWRlcyhwYXR0ZXJuLnJlcGxhY2UoL1xcKi9nLCAnJykpKTtcblx0XHRcdGlmICghc2hvdWxkSW5jbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRzb3VyY2VGaWxlcy5wdXNoKHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0Ly8gU2NhbiBmb3IgdG9wb2xvZ2ljYSBkaXJlY3Rvcnkgc3RydWN0dXJlcyBGSVJTVFxuXHRjb25zdCBwcm9qZWN0RGlyID0gcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCk7XG5cdGNvbnN0IHRvcG9sb2dpY2FEaXJzID0gc2NhblRvcG9sb2dpY2FEaXJlY3Rvcmllcyhwcm9qZWN0RGlyLCBvcHRpb25zLnRvcG9sb2dpY2FEaXJzKTtcblxuXHRpZiAodG9wb2xvZ2ljYURpcnMubGVuZ3RoID4gMCAmJiBvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgRm91bmQgdG9wb2xvZ2ljYSBkaXJlY3RvcmllczogJHt0b3BvbG9naWNhRGlycy5qb2luKCcsICcpfWApO1xuXHR9XG5cblx0Ly8gQW5hbHl6ZSB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIEJFRk9SRSB1c2FnZSBjb2xsZWN0aW9uXG5cdGNvbnN0IHRvcG9sb2dpY2FBbmFseXplciA9IG5ldyBUb3BvbG9naWNhQW5hbHl6ZXIoKTtcblx0Y29uc3QgdG9wb2xvZ2ljYVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIGltcG9ydCgnLi90eXBlcycpLlR5cGVOb2RlPigpO1xuXHRmb3IgKGNvbnN0IGRpciBvZiB0b3BvbG9naWNhRGlycykge1xuXHRcdGNvbnN0IHJlc3VsdCA9IHRvcG9sb2dpY2FBbmFseXplci5hbmFseXplRGlyZWN0b3J5KGRpcik7XG5cdFx0aWYgKHJlc3VsdC50eXBlcy5zaXplID4gMCkge1xuXHRcdFx0Ly8gQ29sbGVjdCB0b3BvbG9naWNhIHR5cGVzIGZvciBkZWZpbml0aW9ucyBhbmQgdXNhZ2UgdHJhY2tpbmdcblx0XHRcdGZvciAoY29uc3QgWyB0eXBlUGF0aCwgbm9kZSBdIG9mIHJlc3VsdC50eXBlcykge1xuXHRcdFx0XHR0b3BvbG9naWNhVHlwZXMuc2V0KHR5cGVQYXRoLCBub2RlKTtcblx0XHRcdH1cblx0XHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdFx0Y29uc29sZS5sb2coYEFkZGVkICR7cmVzdWx0LnR5cGVzLnNpemV9IHR5cGVzIGZyb20gJHtkaXJ9YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChyZXN1bHQuZXJyb3JzLmxlbmd0aCA+IDAgJiYgb3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRyZXN1bHQuZXJyb3JzLmZvckVhY2goZXJyID0+IGNvbnNvbGUud2FybihgW1RvcG9sb2dpY2FdICR7ZXJyfWApKTtcblx0XHR9XG5cdH1cblxuXHQvLyBBZGQgdG9wb2xvZ2ljYSB0eXBlcyB0byBhbmFseXplciBzbyB0aGV5J3JlIGF2YWlsYWJsZSBmb3IgdXNhZ2UgZGV0ZWN0aW9uXG5cdC8vIFByb2Nlc3MgaW4gb3JkZXIgb2YgcGF0aCBkZXB0aCAocGFyZW50cyBmaXJzdCkgdG8gZW5zdXJlIHByb3BlciBoaWVyYXJjaHlcblx0Y29uc3Qgc29ydGVkVHlwZXMgPSBBcnJheS5mcm9tKHRvcG9sb2dpY2FUeXBlcy5lbnRyaWVzKCkpLnNvcnQoKGEsIGIpID0+IHtcblx0XHRjb25zdCBkZXB0aEEgPSAoYVsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRjb25zdCBkZXB0aEIgPSAoYlsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRyZXR1cm4gZGVwdGhBIC0gZGVwdGhCO1xuXHR9KTtcblx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBub2RlIF0gb2Ygc29ydGVkVHlwZXMpIHtcblx0XHRhbmFseXplci5hZGRUb3BvbG9naWNhVHlwZSh0eXBlUGF0aCwgbm9kZSk7XG5cdH1cblxuXHQvLyBGaXJzdCBwYXNzOiBjb2xsZWN0IGFsbCBkZWZpbml0aW9ucy5cblx0Ly8gTW9kdWxlLXNjb3BlIHRyYWNraW5nIChpbXBvcnRzL2V4cG9ydHMgZm9yIG1vZHVsZXMuanNvbikgaGFwcGVucyBpbiB0aGVcblx0Ly8gc2FtZSBwYXNzIOKAlCBpdCBuZWVkcyBvbmx5IHRoZSBBU1QsIG5vdCB0aGUgY29sbGVjdGVkIGRlZmluaXRpb25zLlxuXHRjb25zdCBtb2R1bGVHcmFwaEJ1aWxkZXIgPSBuZXcgTW9kdWxlR3JhcGhCdWlsZGVyKHByb2dyYW0pO1xuXHQvLyBBbmFseXplciBlcnJvcnMgKGUuZy4gYW4gdW5uYW1lZCBsYXp5KCkgY2FsbCkgbmV2ZXIgYWJvcnQgdGhlIHJ1biDigJRcblx0Ly8gdGhlIG9mZmVuZGluZyBjYWxsIGlzIHNpbXBseSBza2lwcGVkIOKAlCBidXQgdGhleSBhcmUgQUxXQVlTIHByaW50ZWQsXG5cdC8vIG9uY2UgZWFjaDogYm90aCBwYXNzZXMgdmlzaXQgdGhlIHNhbWUgY2FsbCBzaXRlcywgc28gZGVkdXBlIGJ5IGtleS5cblx0Y29uc3QgYW5hbHl6ZXJFcnJvcnM6IEFuYWx5emVFcnJvcltdID0gW107XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBBbmFseXppbmcgKGRlZmluaXRpb25zKTogJHtzb3VyY2VGaWxlLmZpbGVOYW1lfWApO1xuXHRcdH1cblxuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCBkZWZpbml0aW9uc1Bhc3MgPSBhbmFseXplci5hbmFseXplRmlsZShzb3VyY2VGaWxlKTtcblx0XHRcdGFuYWx5emVyRXJyb3JzLnB1c2goLi4uZGVmaW5pdGlvbnNQYXNzLmVycm9ycyk7XG5cdFx0XHRtb2R1bGVHcmFwaEJ1aWxkZXIuYWRkRmlsZShzb3VyY2VGaWxlKTtcblx0XHR9IGNhdGNoIChlcnIpIHtcblx0XHRcdGNvbnNvbGUuZXJyb3IoYEVycm9yIGFuYWx5emluZyAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OmAsIGVycik7XG5cdFx0XHR0aHJvdyBlcnI7XG5cdFx0fVxuXHR9XG5cblx0Ly8gU2Vjb25kIHBhc3M6IGNvbGxlY3QgdXNhZ2VzIChub3cgYWxsIGRlZmluaXRpb25zIGFyZSBrbm93biwgaW5jbHVkaW5nIHRvcG9sb2dpY2EpXG5cdGFuYWx5emVyLnJlc2V0VXNhZ2VzKCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBBbmFseXppbmcgKHVzYWdlcyk6ICR7c291cmNlRmlsZS5maWxlTmFtZX1gKTtcblx0XHR9XG5cblx0XHR0cnkge1xuXHRcdFx0Y29uc3QgdXNhZ2VzUGFzcyA9IGFuYWx5emVyLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdFx0YW5hbHl6ZXJFcnJvcnMucHVzaCguLi51c2FnZXNQYXNzLmVycm9ycyk7XG5cdFx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0XHRjb25zb2xlLmVycm9yKGBFcnJvciBhbmFseXppbmcgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfTpgLCBlcnIpO1xuXHRcdFx0dGhyb3cgZXJyO1xuXHRcdH1cblx0fVxuXG5cdGNvbnN0IHNlZW5XYXJuaW5ncyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRmb3IgKGNvbnN0IGFuYWx5emVyRXJyb3Igb2YgYW5hbHl6ZXJFcnJvcnMpIHtcblx0XHRjb25zdCBrZXkgPSBgJHthbmFseXplckVycm9yLmZpbGV9OiR7YW5hbHl6ZXJFcnJvci5saW5lfToke2FuYWx5emVyRXJyb3IuY29sdW1ufToke2FuYWx5emVyRXJyb3IubWVzc2FnZX1gO1xuXHRcdGlmIChzZWVuV2FybmluZ3MuaGFzKGtleSkpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblx0XHRzZWVuV2FybmluZ3MuYWRkKGtleSk7XG5cdFx0Y29uc3QgcmVsRmlsZSA9IHBhdGgucmVsYXRpdmUocHJvamVjdERpciwgYW5hbHl6ZXJFcnJvci5maWxlKTtcblx0XHRjb25zb2xlLndhcm4oYHRhY3RpY2E6ICR7cmVsRmlsZX06JHthbmFseXplckVycm9yLmxpbmV9OiR7YW5hbHl6ZXJFcnJvci5jb2x1bW59ICR7YW5hbHl6ZXJFcnJvci5tZXNzYWdlfWApO1xuXHR9XG5cblx0Ly8gR2VuZXJhdGUgdHlwZXMgZnJvbSBtbmVtb25pY2EgYW5hbHlzaXNcblx0Ly8gTm90ZTogdG9wb2xvZ2ljYSB0eXBlcyBhcmUgYWxyZWFkeSBhZGRlZCB0byB0aGUgYW5hbHl6ZXIncyBncmFwaCB2aWEgYWRkVG9wb2xvZ2ljYVR5cGUoKVxuXHRjb25zdCBncmFwaCA9IGFuYWx5emVyLmdldEdyYXBoKCk7XG5cblx0Ly8gUGF0aC1hd2FyZSBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvbiAoaWRlbnRpdHkgbGF3KTogdGhlIGdlbmVyYXRvclxuXHQvLyByZXNvbHZlcyBuYW1lcyB0aHJvdWdoIHRoZSBzYW1lIHJlbGF0aXZlLWZpcnN0L3Jvb3QvdW5pcXVlIHRpZXJzIHRoZVxuXHQvLyBhbmFseXplciB1c2VzOyB0aGUgYW5hbHl6ZXIncyBvd24gdmFsdWUvaW1wb3J0IHRpZXJzIGFscmVhZHkgdmV0dGVkIHRoZVxuXHQvLyB0eXBlIHN0cmluZ3MgZHVyaW5nIGV4dHJhY3Rpb25cblx0Y29uc3QgcmVmZXJlbmNlUmVzb2x2ZXI6IEdyYXBoUmVmZXJlbmNlUmVzb2x2ZXIgPSAoc2ltcGxlTmFtZSwgYW5jaG9yKSA9PiB7XG5cdFx0Y29uc3QgcmVmUmVzdWx0ID0gcmVzb2x2ZUdyYXBoVHlwZVJlZmVyZW5jZShncmFwaCwgc2ltcGxlTmFtZSwgYW5jaG9yKTtcblx0XHRpZiAocmVmUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdHJldHVybiByZWZSZXN1bHQubm9kZTtcblx0XHR9XG5cdFx0aWYgKHJlZlJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRyZXR1cm4gJ2FtYmlndW91cyc7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH07XG5cdGNvbnN0IGdlbmVyYXRvciA9IG5ldyBUeXBlc0dlbmVyYXRvcihcblx0XHRncmFwaCxcblx0XHRvcHRpb25zLmVzbSxcblx0XHRvcHRpb25zLm91dHB1dERpcixcblx0XHRyZWZlcmVuY2VSZXNvbHZlcixcblx0XHRhbmFseXplci5nZXRCdWlsZGVyVmFsdWVzKClcblx0KTtcblxuXHQvLyBHZW5lcmF0ZSBldmVyeXRoaW5nIGludG8gbWVtb3J5IEZJUlNUIOKAlCB0aGUgaGFyZC1mYWlsIGxhdyBiZWxvdyBtYXlcblx0Ly8gYWJvcnQgdGhlIHJ1biwgYW5kIG5vIC50YWN0aWNhIG91dHB1dCBhdCBhbGwgbWF5IGJlIHdyaXR0ZW4gdGhlblxuXHRjb25zdCBnZW5lcmF0ZWRUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZVR5cGVzRmlsZSgpO1xuXHRjb25zdCByZWdpc3RyeVR5cGVzID0gZ2VuZXJhdG9yLmdlbmVyYXRlVHlwZVJlZ2lzdHJ5KCk7XG5cblx0Ly8gSEFSRCBGQUlMIChncmFwaCBpZGVudGl0eSBsYXcpOiBzYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgbW5lbW9uaWNhXG5cdC8vIGRlZmluaXRpb25zLCBwbHVzIGdyYXBoIHJlZmVyZW5jZXMgdGhhdCBzdGF5IGFtYmlndW91cyBhZnRlclxuXHQvLyBwYXRoLWF3YXJlIHJlc29sdXRpb24gb3IgcmVzb2x2ZSB0byBub3RoaW5nLiBQcmludCBldmVyeSBmYWlsdXJlIHdpdGhcblx0Ly8gYWxsIGl0cyBsb2NhdGlvbnMgYW5kIHdyaXRlIE5PIC50YWN0aWNhIG91dHB1dCBhdCBhbGwuXG5cdGNvbnN0IGZhdGFsRXJyb3JzID0gWyAuLi5hbmFseXplci5nZXRSZXNvbHV0aW9uRXJyb3JzKCksIC4uLmdlbmVyYXRvci5nZXRSZXNvbHV0aW9uRXJyb3JzKCkgXTtcblx0aWYgKGZhdGFsRXJyb3JzLmxlbmd0aCA+IDApIHtcblx0XHRjb25zdCBzZWVuID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0bGV0IHByaW50ZWQgPSAwO1xuXHRcdGZvciAoY29uc3QgZXJyb3Igb2YgZmF0YWxFcnJvcnMpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke2Vycm9yLm1lc3NhZ2V9fCR7ZXJyb3IubG9jYXRpb25zLmpvaW4oJ3wnKX1gO1xuXHRcdFx0aWYgKHNlZW4uaGFzKGtleSkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRzZWVuLmFkZChrZXkpO1xuXHRcdFx0cHJpbnRlZCsrO1xuXHRcdFx0Y29uc29sZS5lcnJvcihgdGFjdGljYTogJHtlcnJvci5tZXNzYWdlfWApO1xuXHRcdFx0Zm9yIChjb25zdCBsb2NhdGlvbiBvZiBlcnJvci5sb2NhdGlvbnMpIHtcblx0XHRcdFx0Y29uc29sZS5lcnJvcihgICBhdCAke2xvY2F0aW9ufWApO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zb2xlLmVycm9yKGB0YWN0aWNhOiBhYm9ydGluZyDigJQgJHtwcmludGVkfSByZXNvbHV0aW9uIGZhaWx1cmUocyk7IG5vIC50YWN0aWNhIG91dHB1dCB3cml0dGVuYCk7XG5cdFx0cmV0dXJuIDE7XG5cdH1cblxuXHQvLyBQcm9qZWN0IHJvb3QgYW5jaG9ycyB0aGUgcmVsYXRpdmUgcGF0aHMgdGhlIHdyaXRlciBlbWl0czogLnRhY3RpY2Fcblx0Ly8gb3V0cHV0IG11c3Qgc3RheSBwb3J0YWJsZSB3aGVuIHRoZSBjaGVja291dCBtb3ZlcyBiZXR3ZWVuIG1hY2hpbmVzLlxuXHQvLyByZXNvbHZlKCkgYm90aCBzaWRlcyDigJQgdHNjb25maWdQYXRoIGl0c2VsZiBtYXkgYmUgcmVsYXRpdmUuXG5cdGNvbnN0IHByb2plY3RSb290ID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpKTtcblx0Y29uc3Qgd3JpdGVyID0gbmV3IFR5cGVzV3JpdGVyKG9wdGlvbnMub3V0cHV0RGlyLCBwcm9qZWN0Um9vdCk7XG5cdC8vIE9uZSBydW46IHRoZSBmaWxlcyBiZWxvdyBhcmUgd3JpdHRlbiB0b2dldGhlciBhdCBjb21taXQoKSwgb3Igbm90XG5cdC8vIGF0IGFsbCB3aGVuIG9ubHkgdGhlaXIgZ2VuZXJhdGVkQXQgc3RhbXBzIHdvdWxkIGNoYW5nZVxuXHR3cml0ZXIuYmVnaW4oKTtcblxuXHRjb25zdCBvdXRwdXRQYXRoID0gd3JpdGVyLndyaXRlVHlwZXNGaWxlKGdlbmVyYXRlZFR5cGVzKTtcblx0Y29uc3QgcmVnaXN0cnlQYXRoID0gd3JpdGVyLndyaXRlVG8oJ3JlZ2lzdHJ5LnRzJywgcmVnaXN0cnlUeXBlcy5jb250ZW50KTtcblxuXHQvLyBHZW5lcmF0ZSBpbmRleC50cyB0byBleHBvcnQgZXZlcnl0aGluZ1xuXHRjb25zdCBpbmRleENvbnRlbnQgPSBgLy8gR2VuZXJhdGVkIGJ5IEBtbmVtb25pY2EvdGFjdGljYSAtIERPIE5PVCBFRElUXG4vLyBFeHBvcnQgYWxsIGdlbmVyYXRlZCB0eXBlc1xuXG5leHBvcnQgKiBmcm9tICcuL3R5cGVzJHtvcHRpb25zLmVzbSA/ICcuanMnIDogJyd9JztcbmV4cG9ydCAqIGZyb20gJy4vcmVnaXN0cnkke29wdGlvbnMuZXNtID8gJy5qcycgOiAnJ30nO1xuYDtcblx0d3JpdGVyLndyaXRlVG8oJ2luZGV4LnRzJywgaW5kZXhDb250ZW50KTtcblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCByZWdpc3RyeS50cyBhdDogJHtyZWdpc3RyeVBhdGh9YCk7XG5cdH1cblxuXHQvLyBHZW5lcmF0ZSBkZWZpbml0aW9ucy5qc29uIGFuZCB1c2FnZXMuanNvbiBmb3IgY29kZSBuYXZpZ2F0aW9uXG5cdC8vIEluY2x1ZGUgYm90aCBtbmVtb25pY2EgYW5kIHRvcG9sb2dpY2EgZGVmaW5pdGlvbnNcblx0Y29uc3QgZGVmaW5pdGlvbnMgPSBuZXcgTWFwKGFuYWx5emVyLmdldERlZmluaXRpb25zKCkpO1xuXHRjb25zdCB1c2FnZXMgPSBuZXcgTWFwKGFuYWx5emVyLmdldFVzYWdlcygpKTtcblx0XG5cdC8vIEFkZCB0b3BvbG9naWNhIHR5cGVzIHRvIGRlZmluaXRpb25zXG5cdGZvciAoY29uc3QgWyBmdWxsUGF0aCwgdHlwZU5vZGUgXSBvZiB0b3BvbG9naWNhVHlwZXMpIHtcblx0XHQvLyBTa2lwIGlmIGFscmVhZHkgZXhpc3RzIChwcmVmZXIgbW5lbW9uaWNhJ3MgYW5hbHlzaXMpXG5cdFx0aWYgKGRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblx0XHRcblx0XHRjb25zdCBkZWZpbml0aW9uOiBpbXBvcnQoJy4vdHlwZXMnKS5EZWZpbml0aW9uSW5mbyA9IHtcblx0XHRcdG5hbWUgICAgICAgIDogdHlwZU5vZGUubmFtZSxcblx0XHRcdGxvY2F0aW9uICAgIDogYCR7dHlwZU5vZGUuc291cmNlRmlsZX06JHt0eXBlTm9kZS5saW5lfToke3R5cGVOb2RlLmNvbHVtbn1gLFxuXHRcdFx0a2luZCAgICAgICAgOiAnZGVmaW5lJyxcblx0XHRcdHBhcmVudCAgICAgIDogdHlwZU5vZGUucGFyZW50ID8gdHlwZU5vZGUucGFyZW50LmZ1bGxQYXRoIDogbnVsbCxcblx0XHRcdHN0cmljdENoYWluIDogdHJ1ZSxcblx0XHRcdGJsb2NrRXJyb3JzIDogZmFsc2Vcblx0XHR9O1xuXHRcdGRlZmluaXRpb25zLnNldChmdWxsUGF0aCwgZGVmaW5pdGlvbik7XG5cdH1cblxuXHQvLyBMb2NhbC1zY29wZSB3YWxrIChpbnN0cnVtZW50YXRpb24gd2Fsa2VyIFBoYXNlIDIpOiBmdW5jdGlvbi9tZXRob2QvYXJyb3dcblx0Ly8gc2NvcGVzIG9ubHkgKG5vIGJsb2NrIHNjb3BlcyDigJQgZGVjaXNpb24gNSksIHZhcmlhYmxlcyB3aXRoIGlzTXV0YWJsZSBhbmRcblx0Ly8gcmVhc3NpZ25tZW50IHNpdGVzIChkZWNpc2lvbiA2KS4gUnVucyBhZnRlciBkZWZpbml0aW9ucyBhcmUga25vd24gc29cblx0Ly8gdmFyaWFibGUgdHlwZVBhdGhzIGNhbiByZXNvbHZlOyBob2xkZXJTY29wZUlkIGlzIGF0dGFjaGVkIHRvIHVzYWdlc1xuXHQvLyBiZWZvcmUgdGhleSBhcmUgd3JpdHRlbi5cblx0Y29uc3Qgc2NvcGVXYWxrZXIgPSBuZXcgTG9jYWxTY29wZVdhbGtlcigpO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRzY29wZVdhbGtlci5hZGRGaWxlKHNvdXJjZUZpbGUpO1xuXHR9XG5cdGNvbnN0IHNjb3BlUmVzb2x2ZXI6IFNjb3BlVHlwZVJlc29sdmVyID0ge1xuXHRcdHJlc29sdmVCeU5hbWUgOiAobmFtZTogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkID0+IHtcblx0XHRcdGlmIChkZWZpbml0aW9ucy5oYXMobmFtZSkpIHtcblx0XHRcdFx0cmV0dXJuIG5hbWU7XG5cdFx0XHR9XG5cdFx0XHRsZXQgZm91bmQ6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0XHRcdGZvciAoY29uc3QgWyBmdWxsUGF0aCwgZGVmaW5pdGlvbiBdIG9mIGRlZmluaXRpb25zKSB7XG5cdFx0XHRcdGlmIChkZWZpbml0aW9uLm5hbWUgIT09IG5hbWUpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRpZiAoZm91bmQpIHtcblx0XHRcdFx0XHQvLyBBbWJpZ3VvdXMgbmFtZSDigJQgbm8gdHlwZSBjaGVja2VyLCBzbyByZWZ1c2UgdG8gZ3Vlc3Ncblx0XHRcdFx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGZvdW5kID0gZnVsbFBhdGg7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gZm91bmQ7XG5cdFx0fSxcblx0XHRoYXNQYXRoIDogKGZ1bGxQYXRoOiBzdHJpbmcpOiBib29sZWFuID0+IHtcblx0XHRcdGNvbnN0IHJlc3VsdCA9IGRlZmluaXRpb25zLmhhcyhmdWxsUGF0aCk7XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH0sXG5cdFx0Ly8gVGhlIGFuYWx5emVyJ3Mgb3duIGxvb2t1cCBsYXcsIGFnYWluc3QgdGhlIHNhbWUgY29tcGxldGUgZ3JhcGggdGhlXG5cdFx0Ly8gdXNhZ2VzIHBhc3MgcmVzb2x2ZWQgd2l0aCDigJQgYSBsb29rdXAoKSBpbml0aWFsaXplciB0aGUgYW5hbHl6ZXJcblx0XHQvLyBhY2NlcHRlZCAoZS5nLiBhbiBpbXBvcnRlZCBIb2xkZXIubG9va3VwKCdUb2tlbicpKSBsYW5kcyB0aGUgc2FtZVxuXHRcdC8vIGZ1bGxQYXRoIGluIHNjb3Blcy5qc29uIGluc3RlYWQgb2Ygc3RhcnZpbmcgdGhlIGNyZWF0aW9uLWdyYXBoXG5cdFx0Ly8gYW5jaG9ycy4gUmVqZWN0ZWQgbG9va3VwcyBzdGF5IHR5cGVQYXRoLWxlc3MgaGVyZTsgdGhlIGFuYWx5emVyXG5cdFx0Ly8gYWxyZWFkeSBoYXJkLWZhaWxlZCB0aGUgcnVuIGFib3ZlLlxuXHRcdHJlc29sdmVMb29rdXAgOiAoY2FsbDogdHMuQ2FsbEV4cHJlc3Npb24pOiBzdHJpbmcgfCB1bmRlZmluZWQgPT4ge1xuXHRcdFx0Y29uc3QgcmVzb2x2ZWQgPSBhbmFseXplci5yZXNvbHZlTG9va3VwQ2FsbFBhdGgoY2FsbCk7XG5cdFx0XHRyZXR1cm4gcmVzb2x2ZWQ7XG5cdFx0fSxcblx0fTtcblx0Y29uc3Qgc2NvcGVBbmFseXNpcyA9IHNjb3BlV2Fsa2VyLmJ1aWxkKHNjb3BlUmVzb2x2ZXIpO1xuXHRMb2NhbFNjb3BlV2Fsa2VyLmF0dGFjaEhvbGRlclNjb3BlSWRzKHVzYWdlcywgc2NvcGVXYWxrZXIpO1xuXG5cdGNvbnN0IGRlZmluaXRpb25zUGF0aCA9IHdyaXRlci53cml0ZURlZmluaXRpb25zRmlsZShkZWZpbml0aW9ucywgZ3JhcGgpO1xuXHRjb25zdCB1c2FnZXNQYXRoID0gd3JpdGVyLndyaXRlVXNhZ2VzRmlsZSh1c2FnZXMpO1xuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGRlZmluaXRpb25zLmpzb24gYXQ6ICR7ZGVmaW5pdGlvbnNQYXRofWApO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgdXNhZ2VzLmpzb24gYXQ6ICR7dXNhZ2VzUGF0aH1gKTtcblx0fVxuXG5cdC8vIERldGVybWluZSBFRFMgc2V0dGluZzogZXhwbGljaXQgZmxhZyA+IGF1dG8tZGV0ZWN0IGRpdmUgPiBkZWZhdWx0IG9mZlxuXHRsZXQgZW5hYmxlRURTID0gb3B0aW9ucy5lZHM7XG5cdGlmIChlbmFibGVFRFMgPT09IHVuZGVmaW5lZCkge1xuXHRcdGVuYWJsZUVEUyA9IGhhc0RpdmVEZXBlbmRlbmN5KHByb2plY3REaXIpO1xuXHR9XG5cblx0aWYgKGVuYWJsZUVEUykge1xuXHRcdGNvbnN0IGVkcyA9IGFuYWx5emVyLmdldEVEU1VzYWdlcygpO1xuXHRcdGF0dGFjaFdyYXBKb2luRGF0YShlZHMsIHNjb3BlV2Fsa2VyLCBzY29wZUFuYWx5c2lzKTtcblx0XHRjb25zdCBlZHNQYXRoID0gd3JpdGVyLndyaXRlRURTRmlsZShlZHMpO1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgZWRzLmpzb24gYXQ6ICR7ZWRzUGF0aH1gKTtcblx0XHR9XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgZmxvdy5qc29uIChuYXRpdmUgaW5zdGFuY2UgdXNhZ2UgdHJhY2tpbmcpXG5cdGNvbnN0IGZsb3cgPSBhbmFseXplci5nZXRGbG93VXNhZ2VzKCk7XG5cdGNvbnN0IGZsb3dQYXRoID0gd3JpdGVyLndyaXRlRmxvd0ZpbGUoZmxvdyk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBmbG93Q291bnQgPSBBcnJheS5mcm9tKGZsb3cudmFsdWVzKCkpLnJlZHVjZSgoc3VtLCBhcnIpID0+IHN1bSArIGFyci5sZW5ndGgsIDApO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgZmxvdy5qc29uIGF0OiAke2Zsb3dQYXRofSAoJHtmbG93Q291bnR9IGZsb3cgZW50cmllcylgKTtcblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBtb2R1bGVzLmpzb24gKG1vZHVsZS1zY29wZSBncmFwaDogaW1wb3J0cy9leHBvcnRzLFxuXHQvLyBkZXBlbmRlbmNpZXMsIGN5Y2xlcywgY3Jvc3MtbW9kdWxlIG1uZW1vbmljYS10eXBlIGVkZ2VzKVxuXHRjb25zdCBkZWZpbmVkVHlwZXNCeUZpbGUgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdGZvciAoY29uc3QgWyBmdWxsUGF0aCwgZGVmaW5pdGlvbiBdIG9mIGRlZmluaXRpb25zKSB7XG5cdFx0Y29uc3QgeyBsb2NhdGlvbiB9ID0gZGVmaW5pdGlvbjtcblx0XHRjb25zdCBsYXN0Q29sb24gPSBsb2NhdGlvbi5sYXN0SW5kZXhPZignOicpO1xuXHRcdGNvbnN0IHByZXZDb2xvbiA9IGxvY2F0aW9uLmxhc3RJbmRleE9mKCc6JywgbGFzdENvbG9uIC0gMSk7XG5cdFx0Y29uc3QgZmlsZSA9IGxvY2F0aW9uLnNsaWNlKDAsIHByZXZDb2xvbik7XG5cdFx0Y29uc3QgbGlzdCA9IGRlZmluZWRUeXBlc0J5RmlsZS5nZXQoZmlsZSkgPz8gW107XG5cdFx0bGlzdC5wdXNoKGZ1bGxQYXRoKTtcblx0XHRkZWZpbmVkVHlwZXNCeUZpbGUuc2V0KGZpbGUsIGxpc3QpO1xuXHR9XG5cdGNvbnN0IG1vZHVsZUdyYXBoID0gbW9kdWxlR3JhcGhCdWlsZGVyLmJ1aWxkKGRlZmluZWRUeXBlc0J5RmlsZSk7XG5cdGNvbnN0IG1vZHVsZXNQYXRoID0gd3JpdGVyLndyaXRlTW9kdWxlc0ZpbGUobW9kdWxlR3JhcGgpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3QgbW9kdWxlQ291bnQgPSBtb2R1bGVHcmFwaC5tb2R1bGVzLnNpemU7XG5cdFx0Y29uc3QgZWRnZUNvdW50ID0gbW9kdWxlR3JhcGguZWRnZXMubGVuZ3RoO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgbW9kdWxlcy5qc29uIGF0OiAke21vZHVsZXNQYXRofSAoJHttb2R1bGVDb3VudH0gbW9kdWxlcywgJHtlZGdlQ291bnR9IGVkZ2VzKWApO1xuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIHNjb3Blcy5qc29uIChsb2NhbC1zY29wZSB3YWxrZXI6IHNjb3BlcywgdmFyaWFibGVzLFxuXHQvLyByZWFzc2lnbm1lbnQgZmxvdy10ZXJtaW5hdGlvbiBwb2ludHMpXG5cdGNvbnN0IHNjb3Blc1BhdGggPSB3cml0ZXIud3JpdGVTY29wZXNGaWxlKHNjb3BlQW5hbHlzaXMpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3Qgc2NvcGVDb3VudCA9IHNjb3BlQW5hbHlzaXMuc2NvcGVzLnNpemU7XG5cdFx0Y29uc3QgdmFyaWFibGVDb3VudCA9IHNjb3BlQW5hbHlzaXMudmFyaWFibGVzLnNpemU7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBzY29wZXMuanNvbiBhdDogJHtzY29wZXNQYXRofSAoJHtzY29wZUNvdW50fSBzY29wZXMsICR7dmFyaWFibGVDb3VudH0gdmFyaWFibGVzKWApO1xuXHR9XG5cblx0Ly8gVGhlIGluc2lkZS1vdXQgY3JlYXRpb24gd2FsayAoaW5zdHJ1bWVudGF0aW9uIHdhbGtlciBQaGFzZSAzKTogYW5jaG9yc1xuXHQvLyBhcmUgdGhlIGluc3RhbnRpYXRpb24gdXNhZ2VzOyBjYWxsZXJzIGFyZSBmb2xsb3dlZCBzYW1lLWZpbGUgYW5kXG5cdC8vIGNyb3NzLWZpbGUgKG1vZHVsZSBncmFwaCwgYmFycmVscyBjaGFzZWQpIHVudGlsIG9ubHkgc3RhcnRlcnMgcmVtYWluLlxuXHRjb25zdCBzb3VyY2VGaWxlc0J5UGF0aCA9IG5ldyBNYXA8c3RyaW5nLCB0cy5Tb3VyY2VGaWxlPigpO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRzb3VyY2VGaWxlc0J5UGF0aC5zZXQocGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUuZmlsZU5hbWUpLCBzb3VyY2VGaWxlKTtcblx0fVxuXHRjb25zdCBjcmVhdGlvbkdyYXBoQnVpbGRlciA9IG5ldyBDcmVhdGlvbkdyYXBoQnVpbGRlcihtb2R1bGVHcmFwaCwgc2NvcGVBbmFseXNpcywgc2NvcGVXYWxrZXIsIHNvdXJjZUZpbGVzQnlQYXRoKTtcblx0Y29uc3QgY3JlYXRpb25HcmFwaCA9IGNyZWF0aW9uR3JhcGhCdWlsZGVyLmJ1aWxkKHVzYWdlcyk7XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIGluc3RydW1lbnRhdGlvbi5qc29uIChmcmFtZXdvcmsgbGlmZWN5Y2xlIGNyb3Nzcm9hZHNcblx0Ly8gZnJvbSB0aGUgbG9hZGVkIHBsdWdpbnMg4oCUIHN5bnRhY3RpYyBkZXRlY3Rpb24gbmVlZHMgbm8gZGl2ZVxuXHQvLyBkZXBlbmRlbmN5LCB1bmxpa2UgZWRzLmpzb24pLiB2MiBjYXJyaWVzIHRoZSBjcmVhdGlvbiBncmFwaFxuXHQvLyBhbG9uZ3NpZGUgdGhlIHBvaW50cy5cblx0Y29uc3QgaW5zdHJ1bWVudGF0aW9uID0gYW5hbHl6ZXIuZ2V0SW5zdHJ1bWVudGF0aW9uUG9pbnRzKCk7XG5cdGNvbnN0IGluc3RydW1lbnRhdGlvblBhdGggPSB3cml0ZXIud3JpdGVJbnN0cnVtZW50YXRpb25GaWxlKGluc3RydW1lbnRhdGlvbiwgY3JlYXRpb25HcmFwaCk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBub2RlQ291bnQgPSBjcmVhdGlvbkdyYXBoLm5vZGVzLmxlbmd0aDtcblx0XHRjb25zdCBlZGdlQ291bnQgPSBjcmVhdGlvbkdyYXBoLmVkZ2VzLmxlbmd0aDtcblx0XHRjb25zdCBhbmNob3JDb3VudCA9IGNyZWF0aW9uR3JhcGguYW5jaG9ycy5sZW5ndGg7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBpbnN0cnVtZW50YXRpb24uanNvbiBhdDogJHtpbnN0cnVtZW50YXRpb25QYXRofSAoJHtpbnN0cnVtZW50YXRpb24ubGVuZ3RofSBwb2ludHMpYCk7XG5cdFx0Y29uc29sZS5sb2coYCAgY3JlYXRpb24gZ3JhcGg6ICR7bm9kZUNvdW50fSBub2RlcywgJHtlZGdlQ291bnR9IGVkZ2VzLCAke2FuY2hvckNvdW50fSBhbmNob3JzYCk7XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgY29udHJvbC5qc29uIChsZXRoZSBjb250cmFjdCwgZm9ybWF0IDEuMik6IHRoZSBzYW1lXG5cdC8vIGNyZWF0aW9uIGdyYXBoIGFuZCBwb2ludHMgYXMgaW5zdHJ1bWVudGF0aW9uLmpzb24sIHJlbmRlcmVkIHVuZGVyIHRoZVxuXHQvLyBjcm9zcy1sYW5ndWFnZSBgY2FsbGVyc2AvYHBvaW50c2Aga2V5cy5cblx0Y29uc3QgY29udHJvbFBhdGggPSB3cml0ZXIud3JpdGVDb250cm9sRmlsZShpbnN0cnVtZW50YXRpb24sIGNyZWF0aW9uR3JhcGgpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBjb250cm9sLmpzb24gYXQ6ICR7Y29udHJvbFBhdGh9YCk7XG5cdH1cblxuXHQvLyBHZW5lcmF0ZSBoaWVyYXJjaHkuanNvbiAoc3RydWN0dXJlZCkgYW5kIGhpZXJhcmNoeS50eHQgKEFTQ0lJIHRyZWUpIGZvciB0aGUgVHJpZVxuXHRjb25zdCBoaWVyYXJjaHlSb290cyA9IGdyYXBoLnRvSGllcmFyY2h5KCk7XG5cdGNvbnN0IGhpZXJhcmNoeUpzb25QYXRoID0gd3JpdGVyLndyaXRlSGllcmFyY2h5RmlsZShoaWVyYXJjaHlSb290cyk7XG5cdGNvbnN0IGhpZXJhcmNoeVRleHQgPSByZW5kZXJUeXBlSGllcmFyY2h5KGdyYXBoKTtcblx0Y29uc3QgaGllcmFyY2h5VHh0UGF0aCA9IHdyaXRlci53cml0ZVRvKCdoaWVyYXJjaHkudHh0JywgaGllcmFyY2h5VGV4dCk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGhpZXJhcmNoeS5qc29uIGF0OiAke2hpZXJhcmNoeUpzb25QYXRofWApO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaGllcmFyY2h5LnR4dCBhdDogJHtoaWVyYXJjaHlUeHRQYXRofWApO1xuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIGNvbGxlY3Rpb25zLmpzb24gKHRoZSBjb2xsZWN0aW9uIG1hbmlmZXN0OiBpZHMsIGRpc3BsYXlcblx0Ly8gbmFtZXMsIE9wdGlvbi1CIHJlZ2lzdHJ5IGludGVyZmFjZXMsIGNhbGwgc2l0ZXMg4oCUIHRoZSBpZOKGlGludGVyZmFjZSBqb2luXG5cdC8vIGtleSBiZXR3ZWVuIHRoZSBwcmVmaXhlZCBncmFwaCBvdXRwdXRzIGFuZCB0aGUgdHlwZXMudHMgYWxpYXNlcylcblx0Y29uc3QgY29sbGVjdGlvbnNQYXRoID0gd3JpdGVyLndyaXRlQ29sbGVjdGlvbnNGaWxlKGFuYWx5emVyLmdldENvbGxlY3Rpb25zTWFuaWZlc3QoKSk7XG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGNvbGxlY3Rpb25zLmpzb24gYXQ6ICR7Y29sbGVjdGlvbnNQYXRofWApO1xuXHR9XG5cblx0Y29uc3Qgd3JpdHRlbiA9IHdyaXRlci5jb21taXQoKTtcblx0Y29uc3QgdW5jaGFuZ2VkTm90ZSA9IHdyaXR0ZW4gPyAnJyA6ICcgKHVuY2hhbmdlZCwgbm90aGluZyB3cml0dGVuKSc7XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgdHlwZXMgYXQ6ICR7b3V0cHV0UGF0aH0ke3VuY2hhbmdlZE5vdGV9YCk7XG5cdFx0Y29uc29sZS5sb2coJ01vZGU6IHR5cGVzIGZpbGUgKGRlZmF1bHQpJyk7XG5cdFx0Y29uc29sZS5sb2coYEZvdW5kICR7Z2VuZXJhdGVkVHlwZXMudHlwZXMubGVuZ3RofSB0eXBlczpgKTtcblx0XHRwcmludFR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHR9IGVsc2Uge1xuXHRcdGNvbnN0IHNob3duRGlyID0gb3B0aW9ucy5vdXRwdXREaXIgfHwgJy50YWN0aWNhJztcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkICR7Z2VuZXJhdGVkVHlwZXMudHlwZXMubGVuZ3RofSB0eXBlcyBhdCAke3Nob3duRGlyfSR7dW5jaGFuZ2VkTm90ZX1gKTtcblx0fVxuXG5cdHJldHVybiAwO1xufVxuXG4vKipcbiAqIFRoZSBkaXJlY3RvcmllcyB0YWN0aWNhIHdyaXRlcywgYXMgYWJzb2x1dGUgcGF0aHM6IHRoZSAtLW91dHB1dCBkaXIgYW5kXG4gKiB0aGUgcHJvamVjdC1jb252ZW50aW9uYWwgLnRhY3RpY2EgZGlyIChuZXh0IHRvIHRzY29uZmlnKS4gVGhlIGNvbnZlbnRpb25hbFxuICogb25lIGlzIEFMV0FZUyBleGNsdWRlZCwgZXZlbiB3aGVuIC0tb3V0cHV0IHBvaW50cyBlbHNld2hlcmU6IGdlbmVyYXRlZFxuICogZmlsZXMgYXJlIG5ldmVyIHByb2plY3Qgc291cmNlLiByZXNvbHZlKCkgYm90aCBzaWRlcyDigJQgdHNjb25maWdQYXRoIG1heVxuICogYmUgcmVsYXRpdmUgKCcuL3RzY29uZmlnLmpzb24nKSB3aGlsZSBmaWxlIG5hbWVzIGFyZSBhYnNvbHV0ZVxuICovXG5mdW5jdGlvbiBnZW5lcmF0ZWRPdXRwdXREaXJzIChvcHRpb25zOiBDTElPcHRpb25zLCB0c2NvbmZpZ1BhdGg6IHN0cmluZyk6IFsgc3RyaW5nLCBzdHJpbmcgXSB7XG5cdGNvbnN0IG91dHB1dERpclBhdGggPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgb3B0aW9ucy5vdXRwdXREaXIgfHwgJy50YWN0aWNhJyk7XG5cdGNvbnN0IGNvbnZlbnRpb25hbE91dHB1dERpciA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKSwgJy50YWN0aWNhJyk7XG5cdGNvbnN0IHJlc3VsdDogWyBzdHJpbmcsIHN0cmluZyBdID0gWyBvdXRwdXREaXJQYXRoLCBjb252ZW50aW9uYWxPdXRwdXREaXIgXTtcblx0cmV0dXJuIHJlc3VsdDtcbn1cblxuLyoqXG4gKiBjaG9raWRhciBvcHRpb25zIGZvciB3YXRjaCBtb2RlLiBUaGUgaW5pdGlhbCBydW4gaGFzIGFscmVhZHkgaGFwcGVuZWQsXG4gKiBzbyBleGlzdGluZyBmaWxlcyBhcmUgbm90IHJlcG9ydGVkIGFzIGFkZGVkIChpZ25vcmVJbml0aWFsOiBvbmUgZnVsbFxuICogcnVuIHBlciBleGlzdGluZyBmaWxlIG90aGVyd2lzZSkuIFRoZSBkaXJlY3RvcmllcyB0YWN0aWNhIHdyaXRlcyBhcmVcbiAqIGFsd2F5cyBpZ25vcmVkLCB3aGF0ZXZlciB0aGUgaW5jbHVkZS9leGNsdWRlIGdsb2JzIHNheTogYSB3cml0dGVuIGZpbGVcbiAqIHdvdWxkIHRyaWdnZXIgYW5vdGhlciBydW4uXG4gKi9cbmZ1bmN0aW9uIHdhdGNoT3B0aW9ucyAob3B0aW9uczogQ0xJT3B0aW9ucywgdHNjb25maWdQYXRoOiBzdHJpbmcpOiB7XG5cdGN3ZCAgICAgICAgICAgOiBzdHJpbmc7XG5cdGlnbm9yZWQgICAgICAgOiAoc3RyaW5nIHwgKChmaWxlUGF0aDogc3RyaW5nKSA9PiBib29sZWFuKSlbXTtcblx0aWdub3JlSW5pdGlhbCA6IGJvb2xlYW47XG5cdHBlcnNpc3RlbnQgICAgOiBib29sZWFuO1xufSB7XG5cdGNvbnN0IHByb2plY3REaXIgPSBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKTtcblx0Y29uc3Qgb3V0cHV0RGlycyA9IGdlbmVyYXRlZE91dHB1dERpcnMob3B0aW9ucywgdHNjb25maWdQYXRoKTtcblx0Y29uc3QgaWdub3JlUGF0aHMgPSBvcHRpb25zLmV4Y2x1ZGUgfHwgWyAnKiovKi5kLnRzJywgJ25vZGVfbW9kdWxlcy8qKicsICcudGFjdGljYS8qKicgXTtcblx0Ly8gY2hva2lkYXIgcGFzc2VzIHBhdGhzIGpvaW5lZCB3aXRoIGN3ZDsgcmVzb2x2ZSgpIGNvdmVycyByZWxhdGl2ZSBvbmVzXG5cdGNvbnN0IGlzR2VuZXJhdGVkID0gKGZpbGVQYXRoOiBzdHJpbmcpOiBib29sZWFuID0+IHtcblx0XHRjb25zdCBhYnNvbHV0ZSA9IHBhdGgucmVzb2x2ZShwcm9qZWN0RGlyLCBmaWxlUGF0aCk7XG5cdFx0Y29uc3QgaW5zaWRlID0gb3V0cHV0RGlycy5zb21lKGRpciA9PiBhYnNvbHV0ZSA9PT0gZGlyIHx8IGFic29sdXRlLnN0YXJ0c1dpdGgoZGlyICsgcGF0aC5zZXApKTtcblx0XHRyZXR1cm4gaW5zaWRlO1xuXHR9O1xuXHRjb25zdCByZXN1bHQgPSB7XG5cdFx0Y3dkICAgICAgICAgICA6IHByb2plY3REaXIsXG5cdFx0aWdub3JlZCAgICAgICA6IFsgLi4uaWdub3JlUGF0aHMsIGlzR2VuZXJhdGVkIF0sXG5cdFx0aWdub3JlSW5pdGlhbCA6IHRydWUsXG5cdFx0cGVyc2lzdGVudCAgICA6IHRydWUsXG5cdH07XG5cdHJldHVybiByZXN1bHQ7XG59XG5cbi8qKlxuICogV2F0Y2ggbW9kZVxuICovXG5mdW5jdGlvbiB3YXRjaCAob3B0aW9uczogQ0xJT3B0aW9ucyk6IHZvaWQge1xuXHRjb25zb2xlLmxvZygnU3RhcnRpbmcgd2F0Y2ggbW9kZS4uLicpO1xuXG5cdC8vIEluaXRpYWwgcnVuXG5cdHJ1bihvcHRpb25zKTtcblxuXHQvLyBTZXQgdXAgZmlsZSB3YXRjaGluZ1xuXHRjb25zdCBjaG9raWRhciA9IHJlcXVpcmUoJ2Nob2tpZGFyJyk7XG5cdGNvbnN0IHRzY29uZmlnUGF0aCA9IGZpbmRUc0NvbmZpZyhvcHRpb25zLnByb2plY3QpO1xuXG5cdGlmICghdHNjb25maWdQYXRoKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6IENvdWxkIG5vdCBmaW5kIHRzY29uZmlnLmpzb24nKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cblxuXHRjb25zdCB3YXRjaFBhdGhzID0gb3B0aW9ucy5pbmNsdWRlIHx8IFsgJyoqLyoudHMnIF07XG5cdGNvbnN0IHdhdGNoZXIgPSBjaG9raWRhci53YXRjaCh3YXRjaFBhdGhzLCB3YXRjaE9wdGlvbnMob3B0aW9ucywgdHNjb25maWdQYXRoKSk7XG5cblx0d2F0Y2hlci5vbignY2hhbmdlJywgKGZpbGVQYXRoOiBzdHJpbmcpID0+IHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgRmlsZSBjaGFuZ2VkOiAke2ZpbGVQYXRofWApO1xuXHRcdH1cblx0XHRydW4ob3B0aW9ucyk7XG5cdH0pO1xuXG5cdHdhdGNoZXIub24oJ2FkZCcsIChmaWxlUGF0aDogc3RyaW5nKSA9PiB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEZpbGUgYWRkZWQ6ICR7ZmlsZVBhdGh9YCk7XG5cdFx0fVxuXHRcdHJ1bihvcHRpb25zKTtcblx0fSk7XG5cblx0Y29uc29sZS5sb2coJ1dhdGNoaW5nIGZvciBjaGFuZ2VzLi4uIChQcmVzcyBDdHJsK0MgdG8gc3RvcCknKTtcbn1cblxuLyoqXG4gKiBNYWluIGVudHJ5IHBvaW50XG4gKi9cbmZ1bmN0aW9uIG1haW4gKCk6IHZvaWQge1xuXHRjb25zdCBhcmdzID0gcHJvY2Vzcy5hcmd2LnNsaWNlKDIpO1xuXHRjb25zdCBvcHRpb25zID0gcGFyc2VBcmdzKGFyZ3MpO1xuXG5cdGlmIChvcHRpb25zLmhlbHApIHtcblx0XHRwcmludEhlbHAoKTtcblx0XHRwcm9jZXNzLmV4aXQoMCk7XG5cdH1cblxuXHR0cnkge1xuXHRcdGlmIChvcHRpb25zLndhdGNoKSB7XG5cdFx0XHR3YXRjaChvcHRpb25zKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0Y29uc3QgY29kZSA9IHJ1bihvcHRpb25zKTtcblx0XHRcdGlmIChjb2RlKSB7XG5cdFx0XHRcdHByb2Nlc3MuZXhpdChjb2RlKTtcblx0XHRcdH1cblx0XHR9XG5cdH0gY2F0Y2ggKGVycm9yKSB7XG5cdFx0Y29uc29sZS5lcnJvcignRXJyb3I6JywgZXJyb3IgaW5zdGFuY2VvZiBFcnJvciA/IGVycm9yLm1lc3NhZ2UgOiBlcnJvcik7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG59XG5cbi8vIFJ1biBpZiBleGVjdXRlZCBkaXJlY3RseVxuaWYgKHJlcXVpcmUubWFpbiA9PT0gbW9kdWxlKSB7XG5cdG1haW4oKTtcbn1cblxuZXhwb3J0IHtcblx0bWFpbiwgcnVuLCB3YXRjaCwgcGFyc2VBcmdzLCB3YXRjaE9wdGlvbnNcbn07XG4iXX0=