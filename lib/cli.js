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
    // Determine output directory for exclusion
    const outputDir = options.outputDir || '.tactica';
    const outputDirPath = path.resolve(process.cwd(), outputDir);
    // The project-conventional .tactica dir (next to tsconfig) is ALWAYS
    // excluded, even when --output points elsewhere: generated files are
    // never project source. resolve() both sides — tsconfigPath may be
    // relative ('./tsconfig.json') while sourceFile.fileName is absolute
    const conventionalOutputDir = path.resolve(process.cwd(), path.dirname(tsconfigPath), '.tactica');
    // a handler importing from either dir names its own generated type
    analyzer.setGeneratedOutputDirs([outputDirPath, conventionalOutputDir]);
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
    if (options.verbose) {
        console.log(`Generated types at: ${outputPath}`);
        console.log('Mode: types file (default)');
        console.log(`Found ${generatedTypes.types.length} types:`);
        printTypeHierarchy(graph);
    }
    else {
        console.log(`Generated ${generatedTypes.types.length} types at ${options.outputDir || '.tactica'}`);
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQXk4Qlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUF2OEI1Qix1Q0FBeUI7QUFDekIsMkNBQTZCO0FBQzdCLG1DQUF1QztBQUN2QywrQ0FBaUM7QUFDakMseUNBQStDO0FBQy9DLCtEQUEyRDtBQUMzRCwyQ0FFcUI7QUFDckIscUNBQXVDO0FBQ3ZDLGlEQUFvRDtBQUNwRCxxREFBd0Q7QUFDeEQscUNBRWtCO0FBQ2xCLG1DQUVpQjtBQTBCakI7O0dBRUc7QUFDSCxTQUFTLFNBQVMsQ0FBRSxJQUFjO0lBQ2pDLE1BQU0sT0FBTyxHQUFlLEVBQUUsQ0FBQztJQUUvQixLQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRSxDQUFDO1FBQ3RDLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBRSxDQUFDLENBQUUsQ0FBQztRQUV0QixRQUFRLEdBQUcsRUFBRSxDQUFDO1lBQ2QsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFNBQVM7Z0JBQ2IsT0FBTyxDQUFDLEtBQUssR0FBRyxJQUFJLENBQUM7Z0JBQ3JCLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssV0FBVztnQkFDZixPQUFPLENBQUMsT0FBTyxHQUFHLElBQUksQ0FBRSxFQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUM5QixNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFVBQVU7Z0JBQ2QsT0FBTyxDQUFDLFNBQVMsR0FBRyxJQUFJLENBQUUsRUFBRSxDQUFDLENBQUUsQ0FBQztnQkFDaEMsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxXQUFX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LENBQUM7UUFDSixJQUFJLE9BQU8sQ0FBQyxLQUFLLEVBQUUsQ0FBQztZQUNuQixLQUFLLENBQUMsT0FBTyxDQUFDLENBQUM7UUFDaEIsQ0FBQzthQUFNLENBQUM7WUFDUCxNQUFNLElBQUksR0FBRyxHQUFHLENBQUMsT0FBTyxDQUFDLENBQUM7WUFDMUIsSUFBSSxJQUFJLEVBQUUsQ0FBQztnQkFDVixPQUFPLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1lBQ3BCLENBQUM7UUFDRixDQUFDO0lBQ0YsQ0FBQztJQUFDLE9BQU8sS0FBSyxFQUFFLENBQUM7UUFDaEIsT0FBTyxDQUFDLEtBQUssQ0FBQyxRQUFRLEVBQUUsS0FBSyxZQUFZLEtBQUssQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLE9BQU8sQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUM7UUFDeEUsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQztJQUNqQixDQUFDO0FBQ0YsQ0FBQztBQUVELDJCQUEyQjtBQUMzQixJQUFJLE9BQU8sQ0FBQyxJQUFJLEtBQUssTUFBTSxFQUFFLENBQUM7SUFDN0IsSUFBSSxFQUFFLENBQUM7QUFDUixDQUFDIiwic291cmNlc0NvbnRlbnQiOlsiIyEvdXNyL2Jpbi9lbnYgbm9kZVxuJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBmcyBmcm9tICdmcyc7XG5pbXBvcnQgKiBhcyBwYXRoIGZyb20gJ3BhdGgnO1xuaW1wb3J0IHsgY3JlYXRlUmVxdWlyZSB9IGZyb20gJ21vZHVsZSc7XG5pbXBvcnQgKiBhcyB0cyBmcm9tICd0eXBlc2NyaXB0JztcbmltcG9ydCB7IE1uZW1vbmljYUFuYWx5emVyIH0gZnJvbSAnLi9hbmFseXplcic7XG5pbXBvcnQgeyBUb3BvbG9naWNhQW5hbHl6ZXIgfSBmcm9tICcuL3RvcG9sb2dpY2EtYW5hbHl6ZXInO1xuaW1wb3J0IHtcblx0VHlwZXNHZW5lcmF0b3IsIEdyYXBoUmVmZXJlbmNlUmVzb2x2ZXIgXG59IGZyb20gJy4vZ2VuZXJhdG9yJztcbmltcG9ydCB7IFR5cGVzV3JpdGVyIH0gZnJvbSAnLi93cml0ZXInO1xuaW1wb3J0IHsgTW9kdWxlR3JhcGhCdWlsZGVyIH0gZnJvbSAnLi9tb2R1bGUtZ3JhcGgnO1xuaW1wb3J0IHsgQ3JlYXRpb25HcmFwaEJ1aWxkZXIgfSBmcm9tICcuL2NyZWF0aW9uLWdyYXBoJztcbmltcG9ydCB7XG5cdExvY2FsU2NvcGVXYWxrZXIsIFNjb3BlVHlwZVJlc29sdmVyXG59IGZyb20gJy4vc2NvcGVzJztcbmltcG9ydCB7XG5cdHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UsIFR5cGVHcmFwaEltcGwgXG59IGZyb20gJy4vZ3JhcGgnO1xuaW1wb3J0IHtcblx0VGFjdGljYUNvbmZpZywgVHlwZU5vZGUsIEVEU0luZm8sIFNjb3BlQW5hbHlzaXMsIEFuYWx5emVFcnJvclxufSBmcm9tICcuL3R5cGVzJztcbmltcG9ydCB7IFRhY3RpY2FQbHVnaW4gfSBmcm9tICcuL3BsdWdpbnMnO1xuXG4vKipcbiAqIENMSSBlbnRyeSBwb2ludCBmb3IgVGFjdGljYVxuICpcbiAqIFJ1bnMgdGhlIGFuYWx5emVyIG92ZXIgYSB0c2NvbmZpZyBwcm9qZWN0IGFuZCB3cml0ZXMgLnRhY3RpY2EvIG91dHB1dFxuICovXG5cbmludGVyZmFjZSBDTElPcHRpb25zIGV4dGVuZHMgVGFjdGljYUNvbmZpZyB7XG5cdHdhdGNoPzogYm9vbGVhbjtcblx0cHJvamVjdD86IHN0cmluZztcblx0aGVscD86IGJvb2xlYW47XG5cdC8qKiBDdXN0b20gdG9wb2xvZ2ljYSBkaXJlY3RvcmllcyB0byBzY2FuICovXG5cdHRvcG9sb2dpY2FEaXJzPzogc3RyaW5nW107XG5cdC8qKiBBZGQgLmpzIGV4dGVuc2lvbnMgdG8gcmVsYXRpdmUgaW1wb3J0cyBmb3IgRVNNIE5vZGVOZXh0IHJlc29sdXRpb24gKi9cblx0ZXNtPzogYm9vbGVhbjtcblx0LyoqIEVuYWJsZSBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHRyYWNraW5nICovXG5cdGVkcz86IGJvb2xlYW47XG5cdC8qKiBQcm9ncmFtbWF0aWMgcGx1Z2luczsgY29uZmlnLWZpbGUgcGx1Z2lucyBhcmUgYXBwZW5kZWQgYWZ0ZXIgdGhlc2UgKi9cblx0cGx1Z2lucz86IFRhY3RpY2FQbHVnaW5bXTtcbn1cblxuLyoqXG4gKiBQYXJzZSBjb21tYW5kIGxpbmUgYXJndW1lbnRzXG4gKi9cbmZ1bmN0aW9uIHBhcnNlQXJncyAoYXJnczogc3RyaW5nW10pOiBDTElPcHRpb25zIHtcblx0Y29uc3Qgb3B0aW9uczogQ0xJT3B0aW9ucyA9IHt9O1xuXG5cdGZvciAobGV0IGkgPSAwOyBpIDwgYXJncy5sZW5ndGg7IGkrKykge1xuXHRcdGNvbnN0IGFyZyA9IGFyZ3NbIGkgXTtcblxuXHRcdHN3aXRjaCAoYXJnKSB7XG5cdFx0Y2FzZSAnLXcnOlxuXHRcdGNhc2UgJy0td2F0Y2gnOlxuXHRcdFx0b3B0aW9ucy53YXRjaCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctcCc6XG5cdFx0Y2FzZSAnLS1wcm9qZWN0Jzpcblx0XHRcdG9wdGlvbnMucHJvamVjdCA9IGFyZ3NbICsraSBdO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLW8nOlxuXHRcdGNhc2UgJy0tb3V0cHV0Jzpcblx0XHRcdG9wdGlvbnMub3V0cHV0RGlyID0gYXJnc1sgKytpIF07XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaSc6XG5cdFx0Y2FzZSAnLS1pbmNsdWRlJzpcblx0XHRcdG9wdGlvbnMuaW5jbHVkZSA9IChvcHRpb25zLmluY2x1ZGUgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1lJzpcblx0XHRjYXNlICctLWV4Y2x1ZGUnOlxuXHRcdFx0b3B0aW9ucy5leGNsdWRlID0gKG9wdGlvbnMuZXhjbHVkZSB8fCBbXSkuY29uY2F0KGFyZ3NbICsraSBdLnNwbGl0KCcsJykpO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXYnOlxuXHRcdGNhc2UgJy0tdmVyYm9zZSc6XG5cdFx0XHRvcHRpb25zLnZlcmJvc2UgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXQnOlxuXHRcdGNhc2UgJy0tdG9wb2xvZ2ljYSc6XG5cdFx0XHRvcHRpb25zLnRvcG9sb2dpY2FEaXJzID0gKG9wdGlvbnMudG9wb2xvZ2ljYURpcnMgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZXNtJzpcblx0XHRcdG9wdGlvbnMuZXNtID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy0tbm8tZWRzJzpcblx0XHRcdG9wdGlvbnMuZWRzID0gZmFsc2U7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctaCc6XG5cdFx0Y2FzZSAnLS1oZWxwJzpcblx0XHRcdG9wdGlvbnMuaGVscCA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gb3B0aW9ucztcbn1cblxuLyoqXG4gKiBQcmludCBoZWxwIG1lc3NhZ2VcbiAqL1xuZnVuY3Rpb24gcHJpbnRIZWxwICgpOiB2b2lkIHtcblx0Y29uc29sZS5sb2coYFxuVGFjdGljYSAtIFR5cGUgZGVmaW5pdGlvbiBnZW5lcmF0b3IgZm9yIE1uZW1vbmljYVxuXG5Vc2FnZTogdGFjdGljYSBbb3B0aW9uc11cblxuT3B0aW9uczpcbiAgLXcsIC0td2F0Y2ggICAgICAgICAgICAgICBXYXRjaCBmb3IgZmlsZSBjaGFuZ2VzIGFuZCByZWdlbmVyYXRlIHR5cGVzXG4gIC1wLCAtLXByb2plY3QgICAgICAgICAgICAgUGF0aCB0byB0c2NvbmZpZy5qc29uIChkZWZhdWx0OiAuL3RzY29uZmlnLmpzb24pXG4gIC1vLCAtLW91dHB1dCAgICAgICAgICAgICAgT3V0cHV0IGRpcmVjdG9yeSBmb3IgZ2VuZXJhdGVkIHR5cGVzIChkZWZhdWx0OiAudGFjdGljYSlcbiAgLWksIC0taW5jbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGluY2x1ZGVcbiAgLWUsIC0tZXhjbHVkZSAgICAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBmaWxlIHBhdHRlcm5zIHRvIGV4Y2x1ZGVcbiAgLXQsIC0tdG9wb2xvZ2ljYSAgICAgICAgICBDb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIHRvIHNjYW5cbiAgLS1lc20gICAgICAgICAgICAgICAgICAgICBBZGQgLmpzIGV4dGVuc2lvbnMgdG8gcmVsYXRpdmUgaW1wb3J0cyAoTm9kZU5leHQgRVNNKVxuICAtLWVkcyAgICAgICAgICAgICAgICAgICAgIEVuYWJsZSBFRFMgKEV4ZWN1dGlvbiBEYXRhIFN0b3JhZ2UpIHRyYWNraW5nXG4gIC0tbm8tZWRzICAgICAgICAgICAgICAgICAgRGlzYWJsZSBFRFMgdHJhY2tpbmdcbiAgLXYsIC0tdmVyYm9zZSAgICAgICAgICAgICBFbmFibGUgdmVyYm9zZSBsb2dnaW5nXG4gIC1oLCAtLWhlbHAgICAgICAgICAgICAgICAgU2hvdyB0aGlzIGhlbHAgbWVzc2FnZVxuXG5Db25maWd1cmF0aW9uOlxuICBGcmFtZXdvcmsgaW5zdHJ1bWVudGF0aW9uIHZvY2FidWxhcnkgaXMgc3VwcGxpZWQgYnkgcGx1Z2lucy4gUGxhY2UgYVxuICAudGFjdGljYS5qcyAob3IgdGFjdGljYS5jb25maWcuanMpIG5leHQgdG8geW91ciB0c2NvbmZpZy5qc29uOlxuXG4gICAgICBtb2R1bGUuZXhwb3J0cyA9IHsgcGx1Z2luczogWyAneW91ci1mcmFtZXdvcmstYWRhcHRlci90YWN0aWNhJyBdIH07XG5cbiAgRW50cmllcyBhcmUgbW9kdWxlIHNwZWNpZmllcnMgKHJlcXVpcmVkIHJlbGF0aXZlIHRvIHRoZSBjb25maWcgZmlsZSkgb3JcbiAgaW5saW5lIHBsdWdpbiBvYmplY3RzLiBXaXRob3V0IHBsdWdpbnMsIGluc3RydW1lbnRhdGlvbi5qc29uIHBvaW50cyA9IFtdLlxuXG5FeGFtcGxlczpcbiAgdGFjdGljYSAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICMgR2VuZXJhdGUgdHlwZXMudHMgYW5kIHJlZ2lzdHJ5LnRzXG4gIHRhY3RpY2EgLS13YXRjaCAgICAgICAgICAgICAgICAgICAgICAjIFdhdGNoIG1vZGVcbiAgdGFjdGljYSAtLXByb2plY3QgLi9zcmMvdHNjb25maWcuanNvbiAjIEN1c3RvbSB0c2NvbmZpZyBwYXRoXG4gIHRhY3RpY2EgLS1vdXRwdXQgLi90eXBlcy9tbmVtb25pY2EgICAjIEN1c3RvbSBvdXRwdXQgZGlyZWN0b3J5XG4gIHRhY3RpY2EgLS10b3BvbG9naWNhIC4vc3JjL2FpLXR5cGVzICAjIFNjYW4gc3BlY2lmaWMgdG9wb2xvZ2ljYSBkaXJlY3RvcnlcbmApO1xufVxuXG4vKipcbiAqIEZpbmQgdHNjb25maWcuanNvblxuICovXG5mdW5jdGlvbiBmaW5kVHNDb25maWcgKHByb2plY3RQYXRoPzogc3RyaW5nKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0aWYgKHByb2plY3RQYXRoKSB7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmMocHJvamVjdFBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gcHJvamVjdFBhdGg7XG5cdFx0fVxuXHRcdHRocm93IG5ldyBFcnJvcihgUHJvamVjdCBmaWxlIG5vdCBmb3VuZDogJHtwcm9qZWN0UGF0aH1gKTtcblx0fVxuXG5cdC8vIExvb2sgZm9yIHRzY29uZmlnLmpzb24gaW4gY3VycmVudCBkaXJlY3RvcnkgYW5kIHBhcmVudCBkaXJlY3Rvcmllc1xuXHRsZXQgY3VycmVudERpciA9IHByb2Nlc3MuY3dkKCk7XG5cdHdoaWxlIChjdXJyZW50RGlyICE9PSBwYXRoLmRpcm5hbWUoY3VycmVudERpcikpIHtcblx0XHRjb25zdCB0c2NvbmZpZ1BhdGggPSBwYXRoLmpvaW4oY3VycmVudERpciwgJ3RzY29uZmlnLmpzb24nKTtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyh0c2NvbmZpZ1BhdGgpKSB7XG5cdFx0XHRyZXR1cm4gdHNjb25maWdQYXRoO1xuXHRcdH1cblx0XHRjdXJyZW50RGlyID0gcGF0aC5kaXJuYW1lKGN1cnJlbnREaXIpO1xuXHR9XG5cblx0cmV0dXJuIHVuZGVmaW5lZDtcbn1cblxuLyoqXG4gKiBMb2FkIFR5cGVTY3JpcHQgcHJvZ3JhbSBmcm9tIHRzY29uZmlnXG4gKi9cbmZ1bmN0aW9uIGxvYWRQcm9ncmFtICh0c2NvbmZpZ1BhdGg6IHN0cmluZyk6IHRzLlByb2dyYW0ge1xuXHRjb25zdCBjb25maWdGaWxlID0gdHMucmVhZENvbmZpZ0ZpbGUodHNjb25maWdQYXRoLCB0cy5zeXMucmVhZEZpbGUpO1xuXG5cdGlmIChjb25maWdGaWxlLmVycm9yKSB7XG5cdFx0Y29uc3QgZXJyb3JUZXh0ID0gdHMuZmxhdHRlbkRpYWdub3N0aWNNZXNzYWdlVGV4dChcblx0XHRcdGNvbmZpZ0ZpbGUuZXJyb3IubWVzc2FnZVRleHQsXG5cdFx0XHQnXFxuJ1xuXHRcdCk7XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBFcnJvciByZWFkaW5nIHRzY29uZmlnOiAke2Vycm9yVGV4dH1gKTtcblx0fVxuXG5cdC8vIFRhY3RpY2EgYW5hbHl6ZXMgd2l0aCBpdHMgb3duIGJ1bmRsZWQgVHlwZVNjcmlwdCwgd2hpY2ggbWF5IGJlIG5ld2VyXG5cdC8vIHRoYW4gdGhlIGNvbXBpbGVyIHRoZSB1c2VyJ3MgdHNjb25maWcgd2FzIHdyaXR0ZW4gZm9yIChlLmcuIGEgVFM1LWVyYVxuXHQvLyBjb25maWcgY2FycnlpbmcgYGJhc2VVcmxgLCBkZXByZWNhdGVkLWVycm9yZWQgYnkgVFM2J3MgVFM1MTAxKS5cblx0Ly8gQW5hbHlzaXMgbmV2ZXIgZW1pdHMgdXNlciBjb2RlLCBzbyBkZXByZWNhdGlvbiBlcnJvcnMgYXJlIGFib3V0IHRoZVxuXHQvLyB1c2VyJ3MgYnVpbGQgcGlwZWxpbmUsIG5vdCBhYm91dCBhbmFseXphYmlsaXR5IOKAlCBzaWxlbmNlIHRoZW0gZm9yIHRoZVxuXHQvLyBhbmFseXNpcyBwcm9ncmFtLiBVbmNvbmRpdGlvbmFsOiBhIHVzZXItcGlubmVkIG9sZGVyIHZhbHVlICgnNS4wJylcblx0Ly8gZG9lcyBub3Qgc2lsZW5jZSA2LjAgZGVwcmVjYXRpb25zIGFuZCB3b3VsZCBzdGlsbCBmYXRhbCBiZWxvdy5cblx0Y29uc3QgcmF3Q29uZmlnID0gY29uZmlnRmlsZS5jb25maWcgPz8ge307XG5cdHJhd0NvbmZpZy5jb21waWxlck9wdGlvbnMgPSB7XG5cdFx0Li4ucmF3Q29uZmlnLmNvbXBpbGVyT3B0aW9ucyxcblx0XHRpZ25vcmVEZXByZWNhdGlvbnMgOiAnNi4wJyxcblx0fTtcblxuXHRjb25zdCBwYXJzZWRDb25maWcgPSB0cy5wYXJzZUpzb25Db25maWdGaWxlQ29udGVudChcblx0XHRyYXdDb25maWcsXG5cdFx0dHMuc3lzLFxuXHRcdHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpXG5cdCk7XG5cblx0aWYgKHBhcnNlZENvbmZpZy5lcnJvcnMubGVuZ3RoID4gMCkge1xuXHRcdGNvbnN0IGVycm9yTWVzc2FnZXMgPSBwYXJzZWRDb25maWcuZXJyb3JzLm1hcChlID0+XG5cdFx0XHR0cy5mbGF0dGVuRGlhZ25vc3RpY01lc3NhZ2VUZXh0KGUubWVzc2FnZVRleHQsICdcXG4nKSk7XG5cdFx0dGhyb3cgbmV3IEVycm9yKGBFcnJvciBwYXJzaW5nIHRzY29uZmlnOiAke2Vycm9yTWVzc2FnZXMuam9pbignXFxuJyl9YCk7XG5cdH1cblxuXHRjb25zdCBwcm9ncmFtID0gdHMuY3JlYXRlUHJvZ3JhbSh7XG5cdFx0cm9vdE5hbWVzIDogcGFyc2VkQ29uZmlnLmZpbGVOYW1lcyxcblx0XHRvcHRpb25zICAgOiBwYXJzZWRDb25maWcub3B0aW9ucyxcblx0fSk7XG5cblx0cmV0dXJuIHByb2dyYW07XG59XG5cbi8qKlxuICogTG9vayB1cCBhIHZhcmlhYmxlIGJ5IG5hbWUgc3RhcnRpbmcgZnJvbSBhIHNjb3BlLCB3YWxraW5nIG91dHdhcmQgdGhyb3VnaFxuICogcGFyZW50U2NvcGVJZC4gVGhlIGlubmVybW9zdCBiaW5kaW5nIHdpbnMgZXZlbiB3aGVuIGl0IGNhcnJpZXMgbm8gdHlwZVBhdGhcbiAqIChzaGFkb3dpbmcgaG9uZXN0eSDigJQgYW4gdW50eXBlZCBsb2NhbCBzaGFkb3dzIGEgdHlwZWQgb3V0ZXIgb25lKS5cbiAqL1xuZnVuY3Rpb24gcmVzb2x2ZVNjb3BlZFZhcmlhYmxlVHlwZVBhdGggKFxuXHRuYW1lOiBzdHJpbmcsXG5cdHNjb3BlSWQ6IHN0cmluZyxcblx0c2NvcGVBbmFseXNpczogU2NvcGVBbmFseXNpc1xuKTogc3RyaW5nIHwgdW5kZWZpbmVkIHtcblx0bGV0IGN1cnJlbnQ6IHN0cmluZyB8IHVuZGVmaW5lZCA9IHNjb3BlSWQ7XG5cdHdoaWxlIChjdXJyZW50KSB7XG5cdFx0Y29uc3QgdmFyaWFibGUgPSBzY29wZUFuYWx5c2lzLnZhcmlhYmxlcy5nZXQoYCR7Y3VycmVudH0jJHtuYW1lfWApO1xuXHRcdGlmICh2YXJpYWJsZSkge1xuXHRcdFx0Y29uc3QgeyB0eXBlUGF0aCB9ID0gdmFyaWFibGU7XG5cdFx0XHRyZXR1cm4gdHlwZVBhdGg7XG5cdFx0fVxuXHRcdGN1cnJlbnQgPSBzY29wZUFuYWx5c2lzLnNjb3Blcy5nZXQoY3VycmVudCk/LnBhcmVudFNjb3BlSWQ7XG5cdH1cblx0cmV0dXJuIHVuZGVmaW5lZDtcbn1cblxuLyoqXG4gKiBKb2luIGRhdGEgZm9yIG1uZW1vZ3JhcGhpY2EncyB3cmFwcGVycyBsYXllcjogcGluIGVhY2ggd3JhcCBlbnRyeSB0byB0aGVcbiAqIHNjb3BlIGhvbGRpbmcgaXRzIGNhbGwgc2l0ZSwgYW5kIHJlc29sdmUgdGhlIHdyYXBwZWQgaW5zdGFuY2UgYXJndW1lbnQnc1xuICogbW5lbW9uaWNhIHR5cGUgdGhyb3VnaCB0aGUgc2NvcGUtdmFyaWFibGUgY2hhaW4uXG4gKi9cbmZ1bmN0aW9uIGF0dGFjaFdyYXBKb2luRGF0YSAoXG5cdGVkczogTWFwPHN0cmluZywgRURTSW5mb1tdPixcblx0c2NvcGVXYWxrZXI6IExvY2FsU2NvcGVXYWxrZXIsXG5cdHNjb3BlQW5hbHlzaXM6IFNjb3BlQW5hbHlzaXNcbik6IHZvaWQge1xuXHRmb3IgKGNvbnN0IGVudHJpZXMgb2YgZWRzLnZhbHVlcygpKSB7XG5cdFx0Zm9yIChjb25zdCBlbnRyeSBvZiBlbnRyaWVzKSB7XG5cdFx0XHRpZiAoZW50cnkua2luZCAhPT0gJ3dyYXAnKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0Y29uc3QgaG9sZGVyU2NvcGVJZCA9IHNjb3BlV2Fsa2VyLmZpbmRIb2xkZXJTY29wZUlkKGVudHJ5LmxvY2F0aW9uKTtcblx0XHRcdGlmICghaG9sZGVyU2NvcGVJZCkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGVudHJ5LnNjb3BlSWQgPSBob2xkZXJTY29wZUlkO1xuXHRcdFx0aWYgKCFlbnRyeS5pbnN0YW5jZUFyZykge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IHdyYXBzVHlwZVBhdGggPSByZXNvbHZlU2NvcGVkVmFyaWFibGVUeXBlUGF0aChcblx0XHRcdFx0ZW50cnkuaW5zdGFuY2VBcmcsXG5cdFx0XHRcdGhvbGRlclNjb3BlSWQsXG5cdFx0XHRcdHNjb3BlQW5hbHlzaXNcblx0XHRcdCk7XG5cdFx0XHRpZiAod3JhcHNUeXBlUGF0aCkge1xuXHRcdFx0XHRlbnRyeS53cmFwc1R5cGVQYXRoID0gd3JhcHNUeXBlUGF0aDtcblx0XHRcdH1cblx0XHR9XG5cdH1cbn1cblxuLyoqXG4gKiBSZW5kZXIgdHlwZSBoaWVyYXJjaHkgYXMgYW4gQVNDSUkgdHJlZSBzdHJpbmcuXG4gKiBEaXNwbGF5LW9ubHk6IHNpYmxpbmdzIGFyZSBzb3J0ZWQgYnkgZnVsbFBhdGggYXQgcmVuZGVyIHRpbWUgKGNvZGUtdW5pdFxuICogb3JkZXIg4oCUIGRlZmF1bHQtY29sbGVjdGlvbiBQYXNjYWxDYXNlIHJvb3RzIGxhbmQgYmVmb3JlIHRoZVxuICogYGNvbGxlY3Rpb25fTjo6YC1wcmVmaXhlZCBvbmVzKS4gVGhlIGdyYXBoIGl0c2VsZiBrZWVwcyBkaXNjb3Zlcnkgb3JkZXI7XG4gKiBoaWVyYXJjaHkuanNvbiBpcyB1bmFmZmVjdGVkLlxuICovXG5mdW5jdGlvbiByZW5kZXJUeXBlSGllcmFyY2h5IChncmFwaDogVHlwZUdyYXBoSW1wbCk6IHN0cmluZyB7XG5cdGNvbnN0IGxpbmVzOiBzdHJpbmdbXSA9IFsgJ1R5cGUgSGllcmFyY2h5IChUcmllKTonIF07XG5cblx0ZnVuY3Rpb24gc29ydGVkQnlGdWxsUGF0aCAobm9kZXM6IFR5cGVOb2RlW10pOiBUeXBlTm9kZVtdIHtcblx0XHRjb25zdCBzb3J0ZWQgPSBBcnJheS5mcm9tKG5vZGVzKTtcblx0XHRzb3J0ZWQuc29ydCgoYSwgYikgPT4ge1xuXHRcdFx0aWYgKGEuZnVsbFBhdGggPCBiLmZ1bGxQYXRoKSB7IHJldHVybiAtMTsgfVxuXHRcdFx0aWYgKGEuZnVsbFBhdGggPiBiLmZ1bGxQYXRoKSB7IHJldHVybiAxOyB9XG5cdFx0XHRyZXR1cm4gMDtcblx0XHR9KTtcblx0XHRyZXR1cm4gc29ydGVkO1xuXHR9XG5cblx0ZnVuY3Rpb24gcmVuZGVyTm9kZSAobm9kZTogVHlwZU5vZGUsIHByZWZpeCA9ICcnLCBpc0xhc3QgPSB0cnVlKTogdm9pZCB7XG5cdFx0Y29uc3QgY29ubmVjdG9yID0gaXNMYXN0ID8gJ+KUlOKUgOKUgCAnIDogJ+KUnOKUgOKUgCAnO1xuXHRcdC8vIFVzZSBub2RlLmZ1bGxQYXRoIGRpcmVjdGx5IGFuZCBjb252ZXJ0IGRvdHMgdG8gdW5kZXJzY29yZXNcblx0XHRjb25zdCBpbnN0YW5jZU5hbWUgPSBub2RlLmZ1bGxQYXRoLnJlcGxhY2UoL1xcLi9nLCAnXycpO1xuXHRcdGxpbmVzLnB1c2goYCR7cHJlZml4fSR7Y29ubmVjdG9yfSR7aW5zdGFuY2VOYW1lfWApO1xuXG5cdFx0Y29uc3QgY2hpbGRyZW4gPSBzb3J0ZWRCeUZ1bGxQYXRoKEFycmF5LmZyb20obm9kZS5jaGlsZHJlbi52YWx1ZXMoKSkpO1xuXHRcdGNvbnN0IG5ld1ByZWZpeCA9IHByZWZpeCArIChpc0xhc3QgPyAnICAgICcgOiAn4pSCICAgJyk7XG5cblx0XHRmb3IgKGxldCBpID0gMDsgaSA8IGNoaWxkcmVuLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRyZW5kZXJOb2RlKGNoaWxkcmVuWyBpIF0sIG5ld1ByZWZpeCwgaSA9PT0gY2hpbGRyZW4ubGVuZ3RoIC0gMSk7XG5cdFx0fVxuXHR9XG5cblx0Y29uc3Qgcm9vdHMgPSBzb3J0ZWRCeUZ1bGxQYXRoKEFycmF5LmZyb20oZ3JhcGgucm9vdHMudmFsdWVzKCkpKTtcblx0Zm9yIChsZXQgaSA9IDA7IGkgPCByb290cy5sZW5ndGg7IGkrKykge1xuXHRcdHJlbmRlck5vZGUocm9vdHNbIGkgXSwgJycsIGkgPT09IHJvb3RzLmxlbmd0aCAtIDEpO1xuXHR9XG5cdC8vIEVtcHR5IGxpbmUgYXQgZW5kXG5cdGxpbmVzLnB1c2goJycpO1xuXG5cdGNvbnN0IHJlc3VsdCA9IGxpbmVzLmpvaW4oJ1xcbicpO1xuXHRyZXR1cm4gcmVzdWx0O1xufVxuXG4vKipcbiAqIFByaW50IHR5cGUgaGllcmFyY2h5IHRvIHRoZSBjb25zb2xlLlxuICovXG5mdW5jdGlvbiBwcmludFR5cGVIaWVyYXJjaHkgKGdyYXBoOiBUeXBlR3JhcGhJbXBsKTogdm9pZCB7XG5cdGNvbnN0IG91dHB1dCA9IHJlbmRlclR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHRjb25zb2xlLmxvZyhvdXRwdXQpO1xufVxuXG4vKipcbiAqIENoZWNrIGlmIEBtbmVtb25pY2EvZGl2ZSBpcyBwcmVzZW50IGluIHBhY2thZ2UuanNvbiBkZXBlbmRlbmNpZXNcbiAqL1xuZnVuY3Rpb24gaGFzRGl2ZURlcGVuZGVuY3kgKHByb2plY3REaXI6IHN0cmluZyk6IGJvb2xlYW4ge1xuXHRjb25zdCBwYWNrYWdlSnNvblBhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgJ3BhY2thZ2UuanNvbicpO1xuXHRpZiAoIWZzLmV4aXN0c1N5bmMocGFja2FnZUpzb25QYXRoKSkge1xuXHRcdHJldHVybiBmYWxzZTtcblx0fVxuXHR0cnkge1xuXHRcdGNvbnN0IGNvbnRlbnQgPSBmcy5yZWFkRmlsZVN5bmMocGFja2FnZUpzb25QYXRoLCAndXRmLTgnKTtcblx0XHRjb25zdCBwa2cgPSBKU09OLnBhcnNlKGNvbnRlbnQpO1xuXHRcdGNvbnN0IGRlcHMgPSBwa2cuZGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdGNvbnN0IGRldkRlcHMgPSBwa2cuZGV2RGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdGNvbnN0IHBlZXJEZXBzID0gcGtnLnBlZXJEZXBlbmRlbmNpZXMgfHwge307XG5cdFx0cmV0dXJuICdAbW5lbW9uaWNhL2RpdmUnIGluIGRlcHMgfHwgJ0BtbmVtb25pY2EvZGl2ZScgaW4gZGV2RGVwcyB8fCAnQG1uZW1vbmljYS9kaXZlJyBpbiBwZWVyRGVwcztcblx0fSBjYXRjaCB7XG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG59XG5cbi8qKlxuICogU2NhbiBmb3IgdG9wb2xvZ2ljYSBkaXJlY3Rvcnkgc3RydWN0dXJlc1xuICovXG5mdW5jdGlvbiBzY2FuVG9wb2xvZ2ljYURpcmVjdG9yaWVzIChwcm9qZWN0RGlyOiBzdHJpbmcsIGN1c3RvbURpcnM/OiBzdHJpbmdbXSk6IHN0cmluZ1tdIHtcblx0Y29uc3QgZGlyczogc3RyaW5nW10gPSBbXTtcblxuXHQvLyBGaXJzdCwgYWRkIGN1c3RvbSBkaXJlY3RvcmllcyBpZiBzcGVjaWZpZWRcblx0aWYgKGN1c3RvbURpcnMpIHtcblx0XHRmb3IgKGNvbnN0IGRpciBvZiBjdXN0b21EaXJzKSB7XG5cdFx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5pc0Fic29sdXRlKGRpcikgPyBkaXIgOiBwYXRoLmpvaW4ocHJvamVjdERpciwgZGlyKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0Y29uc29sZS53YXJuKGBXYXJuaW5nOiBUb3BvbG9naWNhIGRpcmVjdG9yeSBub3QgZm91bmQ6ICR7ZGlyUGF0aH1gKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvLyBUaGVuIGF1dG8tZGlzY292ZXIgc3RhbmRhcmQgdG9wb2xvZ2ljYSBkaXJlY3Rvcmllc1xuXHRjb25zdCBwb3NzaWJsZURpcnMgPSBbICdhaS10eXBlcycsICd0eXBlcycsICd0b3BvbG9naWNhLXR5cGVzJyBdO1xuXG5cdGZvciAoY29uc3QgZGlyTmFtZSBvZiBwb3NzaWJsZURpcnMpIHtcblx0XHRjb25zdCBkaXJQYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsIGRpck5hbWUpO1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdC8vIEF2b2lkIGR1cGxpY2F0ZXNcblx0XHRcdGlmICghZGlycy5pbmNsdWRlcyhkaXJQYXRoKSkge1xuXHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWxzbyBzY2FuIHNyYy8gc3ViZGlyZWN0b3J5XG5cdGNvbnN0IHNyY1BhdGggPSBwYXRoLmpvaW4ocHJvamVjdERpciwgJ3NyYycpO1xuXHRpZiAoZnMuZXhpc3RzU3luYyhzcmNQYXRoKSAmJiBmcy5zdGF0U3luYyhzcmNQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0Zm9yIChjb25zdCBkaXJOYW1lIG9mIHBvc3NpYmxlRGlycykge1xuXHRcdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguam9pbihzcmNQYXRoLCBkaXJOYW1lKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGRpclBhdGgpICYmIGZzLnN0YXRTeW5jKGRpclBhdGgpLmlzRGlyZWN0b3J5KCkpIHtcblx0XHRcdFx0Ly8gQXZvaWQgZHVwbGljYXRlc1xuXHRcdFx0XHRpZiAoIWRpcnMuaW5jbHVkZXMoZGlyUGF0aCkpIHtcblx0XHRcdFx0XHRkaXJzLnB1c2goZGlyUGF0aCk7XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gZGlycztcbn1cblxuLyoqXG4gKiBDb25maWcgZmlsZSBjYW5kaWRhdGVzIChlc2xpbnQtc3R5bGUgcHJvamVjdCBjb25maWcpLCBzZWFyY2hlZCBuZXh0IHRvXG4gKiB0aGUgcmVzb2x2ZWQgdHNjb25maWcgZmlyc3QsIHRoZW4gaW4gdGhlIGN1cnJlbnQgd29ya2luZyBkaXJlY3RvcnkuXG4gKi9cbmNvbnN0IENPTkZJR19GSUxFX05BTUVTID0gWyAnLnRhY3RpY2EuanMnLCAndGFjdGljYS5jb25maWcuanMnIF07XG5cbmludGVyZmFjZSBUYWN0aWNhQ29uZmlnRmlsZSB7XG5cdHBsdWdpbnM/OiBBcnJheTxUYWN0aWNhUGx1Z2luIHwgc3RyaW5nPjtcbn1cblxuLyoqXG4gKiBMb2FkIGZyYW1ld29yay12b2NhYnVsYXJ5IHBsdWdpbnM6IHByb2dyYW1tYXRpYyBvcHRpb25zIGZpcnN0LCB0aGVuIHRoZVxuICogcHJvamVjdCBjb25maWcgZmlsZS4gU3RyaW5nIGVudHJpZXMgYXJlIG1vZHVsZSBzcGVjaWZpZXJzIHJlcXVpcmVkXG4gKiByZWxhdGl2ZSB0byB0aGUgY29uZmlnIGZpbGUgKGUuZy4gYW4gYWRhcHRlciBwYWNrYWdlJ3MgcGx1Z2luIHN1YnBhdGgpLlxuICogV2l0aG91dCBhIGNvbmZpZyBmaWxlIGFuZCB3aXRob3V0IHByb2dyYW1tYXRpYyBwbHVnaW5zIHRoZSBhbmFseXplclxuICogc3RheXMgZnJhbWV3b3JrLWJsaW5kIGFuZCBpbnN0cnVtZW50YXRpb24uanNvbiBjYXJyaWVzIGVtcHR5IHBvaW50cy5cbiAqL1xuZnVuY3Rpb24gbG9hZFRhY3RpY2FQbHVnaW5zIChwcm9qZWN0RGlyOiBzdHJpbmcsIG9wdGlvbnM6IENMSU9wdGlvbnMpOiBUYWN0aWNhUGx1Z2luW10ge1xuXHRjb25zdCBwbHVnaW5zOiBUYWN0aWNhUGx1Z2luW10gPSBbIC4uLihvcHRpb25zLnBsdWdpbnMgfHwgW10pIF07XG5cblx0Y29uc3Qgc2VhcmNoRGlycyA9IFsgcHJvamVjdERpciBdO1xuXHRjb25zdCBjd2QgPSBwcm9jZXNzLmN3ZCgpO1xuXHRpZiAoY3dkICE9PSBwcm9qZWN0RGlyKSB7XG5cdFx0c2VhcmNoRGlycy5wdXNoKGN3ZCk7XG5cdH1cblxuXHRsZXQgY29uZmlnUGF0aDogc3RyaW5nIHwgdW5kZWZpbmVkO1xuXHRmb3IgKGNvbnN0IGRpciBvZiBzZWFyY2hEaXJzKSB7XG5cdFx0Zm9yIChjb25zdCBuYW1lIG9mIENPTkZJR19GSUxFX05BTUVTKSB7XG5cdFx0XHRjb25zdCBjYW5kaWRhdGUgPSBwYXRoLmpvaW4oZGlyLCBuYW1lKTtcblx0XHRcdGlmIChmcy5leGlzdHNTeW5jKGNhbmRpZGF0ZSkpIHtcblx0XHRcdFx0Y29uZmlnUGF0aCA9IGNhbmRpZGF0ZTtcblx0XHRcdFx0YnJlYWs7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChjb25maWdQYXRoKSB7XG5cdFx0XHRicmVhaztcblx0XHR9XG5cdH1cblxuXHRpZiAoIWNvbmZpZ1BhdGgpIHtcblx0XHRyZXR1cm4gcGx1Z2lucztcblx0fVxuXG5cdC8vIGNyZWF0ZVJlcXVpcmUgYW5jaG9yZWQgYXQgdGhlIGNvbmZpZyBmaWxlOiB0aGUgY29uZmlnJ3Mgb3duIGltcG9ydHNcblx0Ly8gYW5kIHN0cmluZyBwbHVnaW4gc3BlY2lmaWVycyByZXNvbHZlIGFnYWluc3QgdGhlIHByb2plY3QncyBtb2R1bGVzXG5cdGNvbnN0IGNvbmZpZ1JlcXVpcmUgPSBjcmVhdGVSZXF1aXJlKGNvbmZpZ1BhdGgpO1xuXHRjb25zdCBsb2FkZWQgPSBjb25maWdSZXF1aXJlKGNvbmZpZ1BhdGgpO1xuXHRjb25zdCBjb25maWc6IFRhY3RpY2FDb25maWdGaWxlID0gbG9hZGVkICYmIHR5cGVvZiBsb2FkZWQgPT09ICdvYmplY3QnICYmICdkZWZhdWx0JyBpbiBsb2FkZWRcblx0XHQ/IGxvYWRlZC5kZWZhdWx0XG5cdFx0OiBsb2FkZWQ7XG5cdGNvbnN0IGVudHJpZXMgPSBjb25maWcgJiYgQXJyYXkuaXNBcnJheShjb25maWcucGx1Z2lucykgPyBjb25maWcucGx1Z2lucyA6IFtdO1xuXG5cdGZvciAoY29uc3QgZW50cnkgb2YgZW50cmllcykge1xuXHRcdGlmICh0eXBlb2YgZW50cnkgIT09ICdzdHJpbmcnKSB7XG5cdFx0XHRwbHVnaW5zLnB1c2goZW50cnkpO1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXHRcdGNvbnN0IG1vZCA9IGNvbmZpZ1JlcXVpcmUoZW50cnkpO1xuXHRcdGNvbnN0IHBsdWdpbjogVGFjdGljYVBsdWdpbiA9IG1vZCAmJiB0eXBlb2YgbW9kID09PSAnb2JqZWN0JyAmJiAnZGVmYXVsdCcgaW4gbW9kXG5cdFx0XHQ/IG1vZC5kZWZhdWx0XG5cdFx0XHQ6IG1vZDtcblx0XHRwbHVnaW5zLnB1c2gocGx1Z2luKTtcblx0fVxuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zdCBuYW1lcyA9IHBsdWdpbnMubWFwKHBsdWdpbiA9PiBwbHVnaW4ubmFtZSB8fCAnKHVubmFtZWQpJykuam9pbignLCAnKTtcblx0XHRjb25zb2xlLmxvZyhgTG9hZGVkIHRhY3RpY2EgY29uZmlnOiAke2NvbmZpZ1BhdGh9IChwbHVnaW5zOiAke25hbWVzIHx8ICdub25lJ30pYCk7XG5cdH1cblxuXHRyZXR1cm4gcGx1Z2lucztcbn1cblxuLyoqXG4gKiBSdW4gdHlwZSBnZW5lcmF0aW9uLiBSZXR1cm5zIDAgb24gc3VjY2VzczsgMSB3aGVuIHRoZSBncmFwaCBpZGVudGl0eSBsYXdcbiAqIGFib3J0ZWQgdGhlIHJ1biAoZmFpbHVyZXMgcHJpbnRlZCwgbm8gLnRhY3RpY2Egb3V0cHV0IHdyaXR0ZW4pLlxuICovXG5mdW5jdGlvbiBydW4gKG9wdGlvbnM6IENMSU9wdGlvbnMpOiBudW1iZXIge1xuXHRjb25zdCB0c2NvbmZpZ1BhdGggPSBmaW5kVHNDb25maWcob3B0aW9ucy5wcm9qZWN0KTtcblxuXHRpZiAoIXRzY29uZmlnUGF0aCkge1xuXHRcdGNvbnNvbGUuZXJyb3IoJ0Vycm9yOiBDb3VsZCBub3QgZmluZCB0c2NvbmZpZy5qc29uJyk7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBVc2luZyB0c2NvbmZpZzogJHt0c2NvbmZpZ1BhdGh9YCk7XG5cdH1cblxuXHQvLyBGcmFtZXdvcmsgdm9jYWJ1bGFyeSBhcnJpdmVzIHZpYSBwbHVnaW5zIOKAlCBhIGNvbmZpZyBmaWxlIG5leHQgdG8gdGhlXG5cdC8vIHRzY29uZmlnIChvciBpbiBjd2QpIGFuZC9vciBwcm9ncmFtbWF0aWMgb3B0aW9ucy4gTm9uZSBsb2FkZWQgbWVhbnNcblx0Ly8gdGhlIGFuYWx5emVyIGRldGVjdHMgemVybyBpbnN0cnVtZW50YXRpb24gcG9pbnRzLlxuXHRjb25zdCBwbHVnaW5zID0gbG9hZFRhY3RpY2FQbHVnaW5zKHBhdGguZGlybmFtZShwYXRoLnJlc29sdmUodHNjb25maWdQYXRoKSksIG9wdGlvbnMpO1xuXG5cdC8vIExvYWQgVHlwZVNjcmlwdCBwcm9ncmFtXG5cdGNvbnN0IHByb2dyYW0gPSBsb2FkUHJvZ3JhbSh0c2NvbmZpZ1BhdGgpO1xuXG5cdC8vIENyZWF0ZSBhbmFseXplclxuXHRjb25zdCBhbmFseXplciA9IG5ldyBNbmVtb25pY2FBbmFseXplcihwcm9ncmFtLCBwbHVnaW5zKTtcblxuXHQvLyBEZXRlcm1pbmUgb3V0cHV0IGRpcmVjdG9yeSBmb3IgZXhjbHVzaW9uXG5cdGNvbnN0IG91dHB1dERpciA9IG9wdGlvbnMub3V0cHV0RGlyIHx8ICcudGFjdGljYSc7XG5cdGNvbnN0IG91dHB1dERpclBhdGggPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgb3V0cHV0RGlyKTtcblx0Ly8gVGhlIHByb2plY3QtY29udmVudGlvbmFsIC50YWN0aWNhIGRpciAobmV4dCB0byB0c2NvbmZpZykgaXMgQUxXQVlTXG5cdC8vIGV4Y2x1ZGVkLCBldmVuIHdoZW4gLS1vdXRwdXQgcG9pbnRzIGVsc2V3aGVyZTogZ2VuZXJhdGVkIGZpbGVzIGFyZVxuXHQvLyBuZXZlciBwcm9qZWN0IHNvdXJjZS4gcmVzb2x2ZSgpIGJvdGggc2lkZXMg4oCUIHRzY29uZmlnUGF0aCBtYXkgYmVcblx0Ly8gcmVsYXRpdmUgKCcuL3RzY29uZmlnLmpzb24nKSB3aGlsZSBzb3VyY2VGaWxlLmZpbGVOYW1lIGlzIGFic29sdXRlXG5cdGNvbnN0IGNvbnZlbnRpb25hbE91dHB1dERpciA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKSwgJy50YWN0aWNhJyk7XG5cdC8vIGEgaGFuZGxlciBpbXBvcnRpbmcgZnJvbSBlaXRoZXIgZGlyIG5hbWVzIGl0cyBvd24gZ2VuZXJhdGVkIHR5cGVcblx0YW5hbHl6ZXIuc2V0R2VuZXJhdGVkT3V0cHV0RGlycyhbIG91dHB1dERpclBhdGgsIGNvbnZlbnRpb25hbE91dHB1dERpciBdKTtcblxuXHQvLyBDb2xsZWN0IHNvdXJjZSBmaWxlcyB0byBhbmFseXplXG5cdGNvbnN0IHNvdXJjZUZpbGVzOiB0cy5Tb3VyY2VGaWxlW10gPSBbXTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHByb2dyYW0uZ2V0U291cmNlRmlsZXMoKSkge1xuXHRcdGlmIChzb3VyY2VGaWxlLmlzRGVjbGFyYXRpb25GaWxlKSB7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cblx0XHRjb25zdCBhYnNvbHV0ZUZpbGVOYW1lID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIHNvdXJjZUZpbGUuZmlsZU5hbWUpO1xuXHRcdGlmIChhYnNvbHV0ZUZpbGVOYW1lLnN0YXJ0c1dpdGgob3V0cHV0RGlyUGF0aCArIHBhdGguc2VwKSB8fFxuXHRcdFx0YWJzb2x1dGVGaWxlTmFtZS5zdGFydHNXaXRoKGNvbnZlbnRpb25hbE91dHB1dERpciArIHBhdGguc2VwKSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgZXhjbHVkZSBwYXR0ZXJuc1xuXHRcdGlmIChvcHRpb25zLmV4Y2x1ZGUpIHtcblx0XHRcdGNvbnN0IHNob3VsZEV4Y2x1ZGUgPSBvcHRpb25zLmV4Y2x1ZGUuc29tZShwYXR0ZXJuID0+XG5cdFx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUuaW5jbHVkZXMocGF0dGVybi5yZXBsYWNlKC9cXCovZywgJycpKSk7XG5cdFx0XHRpZiAoc2hvdWxkRXhjbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBDaGVjayBpbmNsdWRlIHBhdHRlcm5zXG5cdFx0aWYgKG9wdGlvbnMuaW5jbHVkZSAmJiBvcHRpb25zLmluY2x1ZGUubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3Qgc2hvdWxkSW5jbHVkZSA9IG9wdGlvbnMuaW5jbHVkZS5zb21lKHBhdHRlcm4gPT5cblx0XHRcdFx0c291cmNlRmlsZS5maWxlTmFtZS5pbmNsdWRlcyhwYXR0ZXJuLnJlcGxhY2UoL1xcKi9nLCAnJykpKTtcblx0XHRcdGlmICghc2hvdWxkSW5jbHVkZSkge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRzb3VyY2VGaWxlcy5wdXNoKHNvdXJjZUZpbGUpO1xuXHR9XG5cblx0Ly8gU2NhbiBmb3IgdG9wb2xvZ2ljYSBkaXJlY3Rvcnkgc3RydWN0dXJlcyBGSVJTVFxuXHRjb25zdCBwcm9qZWN0RGlyID0gcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCk7XG5cdGNvbnN0IHRvcG9sb2dpY2FEaXJzID0gc2NhblRvcG9sb2dpY2FEaXJlY3Rvcmllcyhwcm9qZWN0RGlyLCBvcHRpb25zLnRvcG9sb2dpY2FEaXJzKTtcblxuXHRpZiAodG9wb2xvZ2ljYURpcnMubGVuZ3RoID4gMCAmJiBvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgRm91bmQgdG9wb2xvZ2ljYSBkaXJlY3RvcmllczogJHt0b3BvbG9naWNhRGlycy5qb2luKCcsICcpfWApO1xuXHR9XG5cblx0Ly8gQW5hbHl6ZSB0b3BvbG9naWNhIGRpcmVjdG9yaWVzIEJFRk9SRSB1c2FnZSBjb2xsZWN0aW9uXG5cdGNvbnN0IHRvcG9sb2dpY2FBbmFseXplciA9IG5ldyBUb3BvbG9naWNhQW5hbHl6ZXIoKTtcblx0Y29uc3QgdG9wb2xvZ2ljYVR5cGVzID0gbmV3IE1hcDxzdHJpbmcsIGltcG9ydCgnLi90eXBlcycpLlR5cGVOb2RlPigpO1xuXHRmb3IgKGNvbnN0IGRpciBvZiB0b3BvbG9naWNhRGlycykge1xuXHRcdGNvbnN0IHJlc3VsdCA9IHRvcG9sb2dpY2FBbmFseXplci5hbmFseXplRGlyZWN0b3J5KGRpcik7XG5cdFx0aWYgKHJlc3VsdC50eXBlcy5zaXplID4gMCkge1xuXHRcdFx0Ly8gQ29sbGVjdCB0b3BvbG9naWNhIHR5cGVzIGZvciBkZWZpbml0aW9ucyBhbmQgdXNhZ2UgdHJhY2tpbmdcblx0XHRcdGZvciAoY29uc3QgWyB0eXBlUGF0aCwgbm9kZSBdIG9mIHJlc3VsdC50eXBlcykge1xuXHRcdFx0XHR0b3BvbG9naWNhVHlwZXMuc2V0KHR5cGVQYXRoLCBub2RlKTtcblx0XHRcdH1cblx0XHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdFx0Y29uc29sZS5sb2coYEFkZGVkICR7cmVzdWx0LnR5cGVzLnNpemV9IHR5cGVzIGZyb20gJHtkaXJ9YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGlmIChyZXN1bHQuZXJyb3JzLmxlbmd0aCA+IDAgJiYgb3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRyZXN1bHQuZXJyb3JzLmZvckVhY2goZXJyID0+IGNvbnNvbGUud2FybihgW1RvcG9sb2dpY2FdICR7ZXJyfWApKTtcblx0XHR9XG5cdH1cblxuXHQvLyBBZGQgdG9wb2xvZ2ljYSB0eXBlcyB0byBhbmFseXplciBzbyB0aGV5J3JlIGF2YWlsYWJsZSBmb3IgdXNhZ2UgZGV0ZWN0aW9uXG5cdC8vIFByb2Nlc3MgaW4gb3JkZXIgb2YgcGF0aCBkZXB0aCAocGFyZW50cyBmaXJzdCkgdG8gZW5zdXJlIHByb3BlciBoaWVyYXJjaHlcblx0Y29uc3Qgc29ydGVkVHlwZXMgPSBBcnJheS5mcm9tKHRvcG9sb2dpY2FUeXBlcy5lbnRyaWVzKCkpLnNvcnQoKGEsIGIpID0+IHtcblx0XHRjb25zdCBkZXB0aEEgPSAoYVsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRjb25zdCBkZXB0aEIgPSAoYlsgMCBdLm1hdGNoKC9cXC4vZykgfHwgW10pLmxlbmd0aDtcblx0XHRyZXR1cm4gZGVwdGhBIC0gZGVwdGhCO1xuXHR9KTtcblx0Zm9yIChjb25zdCBbIHR5cGVQYXRoLCBub2RlIF0gb2Ygc29ydGVkVHlwZXMpIHtcblx0XHRhbmFseXplci5hZGRUb3BvbG9naWNhVHlwZSh0eXBlUGF0aCwgbm9kZSk7XG5cdH1cblxuXHQvLyBGaXJzdCBwYXNzOiBjb2xsZWN0IGFsbCBkZWZpbml0aW9ucy5cblx0Ly8gTW9kdWxlLXNjb3BlIHRyYWNraW5nIChpbXBvcnRzL2V4cG9ydHMgZm9yIG1vZHVsZXMuanNvbikgaGFwcGVucyBpbiB0aGVcblx0Ly8gc2FtZSBwYXNzIOKAlCBpdCBuZWVkcyBvbmx5IHRoZSBBU1QsIG5vdCB0aGUgY29sbGVjdGVkIGRlZmluaXRpb25zLlxuXHRjb25zdCBtb2R1bGVHcmFwaEJ1aWxkZXIgPSBuZXcgTW9kdWxlR3JhcGhCdWlsZGVyKHByb2dyYW0pO1xuXHQvLyBBbmFseXplciBlcnJvcnMgKGUuZy4gYW4gdW5uYW1lZCBsYXp5KCkgY2FsbCkgbmV2ZXIgYWJvcnQgdGhlIHJ1biDigJRcblx0Ly8gdGhlIG9mZmVuZGluZyBjYWxsIGlzIHNpbXBseSBza2lwcGVkIOKAlCBidXQgdGhleSBhcmUgQUxXQVlTIHByaW50ZWQsXG5cdC8vIG9uY2UgZWFjaDogYm90aCBwYXNzZXMgdmlzaXQgdGhlIHNhbWUgY2FsbCBzaXRlcywgc28gZGVkdXBlIGJ5IGtleS5cblx0Y29uc3QgYW5hbHl6ZXJFcnJvcnM6IEFuYWx5emVFcnJvcltdID0gW107XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBBbmFseXppbmcgKGRlZmluaXRpb25zKTogJHtzb3VyY2VGaWxlLmZpbGVOYW1lfWApO1xuXHRcdH1cblxuXHRcdHRyeSB7XG5cdFx0XHRjb25zdCBkZWZpbml0aW9uc1Bhc3MgPSBhbmFseXplci5hbmFseXplRmlsZShzb3VyY2VGaWxlKTtcblx0XHRcdGFuYWx5emVyRXJyb3JzLnB1c2goLi4uZGVmaW5pdGlvbnNQYXNzLmVycm9ycyk7XG5cdFx0XHRtb2R1bGVHcmFwaEJ1aWxkZXIuYWRkRmlsZShzb3VyY2VGaWxlKTtcblx0XHR9IGNhdGNoIChlcnIpIHtcblx0XHRcdGNvbnNvbGUuZXJyb3IoYEVycm9yIGFuYWx5emluZyAke3NvdXJjZUZpbGUuZmlsZU5hbWV9OmAsIGVycik7XG5cdFx0XHR0aHJvdyBlcnI7XG5cdFx0fVxuXHR9XG5cblx0Ly8gU2Vjb25kIHBhc3M6IGNvbGxlY3QgdXNhZ2VzIChub3cgYWxsIGRlZmluaXRpb25zIGFyZSBrbm93biwgaW5jbHVkaW5nIHRvcG9sb2dpY2EpXG5cdGFuYWx5emVyLnJlc2V0VXNhZ2VzKCk7XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBzb3VyY2VGaWxlcykge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBBbmFseXppbmcgKHVzYWdlcyk6ICR7c291cmNlRmlsZS5maWxlTmFtZX1gKTtcblx0XHR9XG5cblx0XHR0cnkge1xuXHRcdFx0Y29uc3QgdXNhZ2VzUGFzcyA9IGFuYWx5emVyLmFuYWx5emVGaWxlKHNvdXJjZUZpbGUpO1xuXHRcdFx0YW5hbHl6ZXJFcnJvcnMucHVzaCguLi51c2FnZXNQYXNzLmVycm9ycyk7XG5cdFx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0XHRjb25zb2xlLmVycm9yKGBFcnJvciBhbmFseXppbmcgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfTpgLCBlcnIpO1xuXHRcdFx0dGhyb3cgZXJyO1xuXHRcdH1cblx0fVxuXG5cdGNvbnN0IHNlZW5XYXJuaW5ncyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRmb3IgKGNvbnN0IGFuYWx5emVyRXJyb3Igb2YgYW5hbHl6ZXJFcnJvcnMpIHtcblx0XHRjb25zdCBrZXkgPSBgJHthbmFseXplckVycm9yLmZpbGV9OiR7YW5hbHl6ZXJFcnJvci5saW5lfToke2FuYWx5emVyRXJyb3IuY29sdW1ufToke2FuYWx5emVyRXJyb3IubWVzc2FnZX1gO1xuXHRcdGlmIChzZWVuV2FybmluZ3MuaGFzKGtleSkpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblx0XHRzZWVuV2FybmluZ3MuYWRkKGtleSk7XG5cdFx0Y29uc3QgcmVsRmlsZSA9IHBhdGgucmVsYXRpdmUocHJvamVjdERpciwgYW5hbHl6ZXJFcnJvci5maWxlKTtcblx0XHRjb25zb2xlLndhcm4oYHRhY3RpY2E6ICR7cmVsRmlsZX06JHthbmFseXplckVycm9yLmxpbmV9OiR7YW5hbHl6ZXJFcnJvci5jb2x1bW59ICR7YW5hbHl6ZXJFcnJvci5tZXNzYWdlfWApO1xuXHR9XG5cblx0Ly8gR2VuZXJhdGUgdHlwZXMgZnJvbSBtbmVtb25pY2EgYW5hbHlzaXNcblx0Ly8gTm90ZTogdG9wb2xvZ2ljYSB0eXBlcyBhcmUgYWxyZWFkeSBhZGRlZCB0byB0aGUgYW5hbHl6ZXIncyBncmFwaCB2aWEgYWRkVG9wb2xvZ2ljYVR5cGUoKVxuXHRjb25zdCBncmFwaCA9IGFuYWx5emVyLmdldEdyYXBoKCk7XG5cblx0Ly8gUGF0aC1hd2FyZSBncmFwaCByZWZlcmVuY2UgcmVzb2x1dGlvbiAoaWRlbnRpdHkgbGF3KTogdGhlIGdlbmVyYXRvclxuXHQvLyByZXNvbHZlcyBuYW1lcyB0aHJvdWdoIHRoZSBzYW1lIHJlbGF0aXZlLWZpcnN0L3Jvb3QvdW5pcXVlIHRpZXJzIHRoZVxuXHQvLyBhbmFseXplciB1c2VzOyB0aGUgYW5hbHl6ZXIncyBvd24gdmFsdWUvaW1wb3J0IHRpZXJzIGFscmVhZHkgdmV0dGVkIHRoZVxuXHQvLyB0eXBlIHN0cmluZ3MgZHVyaW5nIGV4dHJhY3Rpb25cblx0Y29uc3QgcmVmZXJlbmNlUmVzb2x2ZXI6IEdyYXBoUmVmZXJlbmNlUmVzb2x2ZXIgPSAoc2ltcGxlTmFtZSwgYW5jaG9yKSA9PiB7XG5cdFx0Y29uc3QgcmVmUmVzdWx0ID0gcmVzb2x2ZUdyYXBoVHlwZVJlZmVyZW5jZShncmFwaCwgc2ltcGxlTmFtZSwgYW5jaG9yKTtcblx0XHRpZiAocmVmUmVzdWx0LnN0YXR1cyA9PT0gJ3VuaXF1ZScpIHtcblx0XHRcdHJldHVybiByZWZSZXN1bHQubm9kZTtcblx0XHR9XG5cdFx0aWYgKHJlZlJlc3VsdC5zdGF0dXMgPT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRyZXR1cm4gJ2FtYmlndW91cyc7XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH07XG5cdGNvbnN0IGdlbmVyYXRvciA9IG5ldyBUeXBlc0dlbmVyYXRvcihcblx0XHRncmFwaCxcblx0XHRvcHRpb25zLmVzbSxcblx0XHRvcHRpb25zLm91dHB1dERpcixcblx0XHRyZWZlcmVuY2VSZXNvbHZlcixcblx0XHRhbmFseXplci5nZXRCdWlsZGVyVmFsdWVzKClcblx0KTtcblxuXHQvLyBHZW5lcmF0ZSBldmVyeXRoaW5nIGludG8gbWVtb3J5IEZJUlNUIOKAlCB0aGUgaGFyZC1mYWlsIGxhdyBiZWxvdyBtYXlcblx0Ly8gYWJvcnQgdGhlIHJ1biwgYW5kIG5vIC50YWN0aWNhIG91dHB1dCBhdCBhbGwgbWF5IGJlIHdyaXR0ZW4gdGhlblxuXHRjb25zdCBnZW5lcmF0ZWRUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZVR5cGVzRmlsZSgpO1xuXHRjb25zdCByZWdpc3RyeVR5cGVzID0gZ2VuZXJhdG9yLmdlbmVyYXRlVHlwZVJlZ2lzdHJ5KCk7XG5cblx0Ly8gSEFSRCBGQUlMIChncmFwaCBpZGVudGl0eSBsYXcpOiBzYW1lLW5hbWVzcGFjZSBkdXBsaWNhdGUgbW5lbW9uaWNhXG5cdC8vIGRlZmluaXRpb25zLCBwbHVzIGdyYXBoIHJlZmVyZW5jZXMgdGhhdCBzdGF5IGFtYmlndW91cyBhZnRlclxuXHQvLyBwYXRoLWF3YXJlIHJlc29sdXRpb24gb3IgcmVzb2x2ZSB0byBub3RoaW5nLiBQcmludCBldmVyeSBmYWlsdXJlIHdpdGhcblx0Ly8gYWxsIGl0cyBsb2NhdGlvbnMgYW5kIHdyaXRlIE5PIC50YWN0aWNhIG91dHB1dCBhdCBhbGwuXG5cdGNvbnN0IGZhdGFsRXJyb3JzID0gWyAuLi5hbmFseXplci5nZXRSZXNvbHV0aW9uRXJyb3JzKCksIC4uLmdlbmVyYXRvci5nZXRSZXNvbHV0aW9uRXJyb3JzKCkgXTtcblx0aWYgKGZhdGFsRXJyb3JzLmxlbmd0aCA+IDApIHtcblx0XHRjb25zdCBzZWVuID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0bGV0IHByaW50ZWQgPSAwO1xuXHRcdGZvciAoY29uc3QgZXJyb3Igb2YgZmF0YWxFcnJvcnMpIHtcblx0XHRcdGNvbnN0IGtleSA9IGAke2Vycm9yLm1lc3NhZ2V9fCR7ZXJyb3IubG9jYXRpb25zLmpvaW4oJ3wnKX1gO1xuXHRcdFx0aWYgKHNlZW4uaGFzKGtleSkpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRzZWVuLmFkZChrZXkpO1xuXHRcdFx0cHJpbnRlZCsrO1xuXHRcdFx0Y29uc29sZS5lcnJvcihgdGFjdGljYTogJHtlcnJvci5tZXNzYWdlfWApO1xuXHRcdFx0Zm9yIChjb25zdCBsb2NhdGlvbiBvZiBlcnJvci5sb2NhdGlvbnMpIHtcblx0XHRcdFx0Y29uc29sZS5lcnJvcihgICBhdCAke2xvY2F0aW9ufWApO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zb2xlLmVycm9yKGB0YWN0aWNhOiBhYm9ydGluZyDigJQgJHtwcmludGVkfSByZXNvbHV0aW9uIGZhaWx1cmUocyk7IG5vIC50YWN0aWNhIG91dHB1dCB3cml0dGVuYCk7XG5cdFx0cmV0dXJuIDE7XG5cdH1cblxuXHQvLyBQcm9qZWN0IHJvb3QgYW5jaG9ycyB0aGUgcmVsYXRpdmUgcGF0aHMgdGhlIHdyaXRlciBlbWl0czogLnRhY3RpY2Fcblx0Ly8gb3V0cHV0IG11c3Qgc3RheSBwb3J0YWJsZSB3aGVuIHRoZSBjaGVja291dCBtb3ZlcyBiZXR3ZWVuIG1hY2hpbmVzLlxuXHQvLyByZXNvbHZlKCkgYm90aCBzaWRlcyDigJQgdHNjb25maWdQYXRoIGl0c2VsZiBtYXkgYmUgcmVsYXRpdmUuXG5cdGNvbnN0IHByb2plY3RSb290ID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpKTtcblx0Y29uc3Qgd3JpdGVyID0gbmV3IFR5cGVzV3JpdGVyKG9wdGlvbnMub3V0cHV0RGlyLCBwcm9qZWN0Um9vdCk7XG5cblx0Y29uc3Qgb3V0cHV0UGF0aCA9IHdyaXRlci53cml0ZVR5cGVzRmlsZShnZW5lcmF0ZWRUeXBlcyk7XG5cdGNvbnN0IHJlZ2lzdHJ5UGF0aCA9IHdyaXRlci53cml0ZVRvKCdyZWdpc3RyeS50cycsIHJlZ2lzdHJ5VHlwZXMuY29udGVudCk7XG5cblx0Ly8gR2VuZXJhdGUgaW5kZXgudHMgdG8gZXhwb3J0IGV2ZXJ5dGhpbmdcblx0Y29uc3QgaW5kZXhDb250ZW50ID0gYC8vIEdlbmVyYXRlZCBieSBAbW5lbW9uaWNhL3RhY3RpY2EgLSBETyBOT1QgRURJVFxuLy8gRXhwb3J0IGFsbCBnZW5lcmF0ZWQgdHlwZXNcblxuZXhwb3J0ICogZnJvbSAnLi90eXBlcyR7b3B0aW9ucy5lc20gPyAnLmpzJyA6ICcnfSc7XG5leHBvcnQgKiBmcm9tICcuL3JlZ2lzdHJ5JHtvcHRpb25zLmVzbSA/ICcuanMnIDogJyd9JztcbmA7XG5cdHdyaXRlci53cml0ZVRvKCdpbmRleC50cycsIGluZGV4Q29udGVudCk7XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgcmVnaXN0cnkudHMgYXQ6ICR7cmVnaXN0cnlQYXRofWApO1xuXHR9XG5cblx0Ly8gR2VuZXJhdGUgZGVmaW5pdGlvbnMuanNvbiBhbmQgdXNhZ2VzLmpzb24gZm9yIGNvZGUgbmF2aWdhdGlvblxuXHQvLyBJbmNsdWRlIGJvdGggbW5lbW9uaWNhIGFuZCB0b3BvbG9naWNhIGRlZmluaXRpb25zXG5cdGNvbnN0IGRlZmluaXRpb25zID0gbmV3IE1hcChhbmFseXplci5nZXREZWZpbml0aW9ucygpKTtcblx0Y29uc3QgdXNhZ2VzID0gbmV3IE1hcChhbmFseXplci5nZXRVc2FnZXMoKSk7XG5cdFxuXHQvLyBBZGQgdG9wb2xvZ2ljYSB0eXBlcyB0byBkZWZpbml0aW9uc1xuXHRmb3IgKGNvbnN0IFsgZnVsbFBhdGgsIHR5cGVOb2RlIF0gb2YgdG9wb2xvZ2ljYVR5cGVzKSB7XG5cdFx0Ly8gU2tpcCBpZiBhbHJlYWR5IGV4aXN0cyAocHJlZmVyIG1uZW1vbmljYSdzIGFuYWx5c2lzKVxuXHRcdGlmIChkZWZpbml0aW9ucy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cdFx0XG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogaW1wb3J0KCcuL3R5cGVzJykuRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOb2RlLm5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3R5cGVOb2RlLnNvdXJjZUZpbGV9OiR7dHlwZU5vZGUubGluZX06JHt0eXBlTm9kZS5jb2x1bW59YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHR5cGVOb2RlLnBhcmVudCA/IHR5cGVOb2RlLnBhcmVudC5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGZhbHNlXG5cdFx0fTtcblx0XHRkZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHR9XG5cblx0Ly8gTG9jYWwtc2NvcGUgd2FsayAoaW5zdHJ1bWVudGF0aW9uIHdhbGtlciBQaGFzZSAyKTogZnVuY3Rpb24vbWV0aG9kL2Fycm93XG5cdC8vIHNjb3BlcyBvbmx5IChubyBibG9jayBzY29wZXMg4oCUIGRlY2lzaW9uIDUpLCB2YXJpYWJsZXMgd2l0aCBpc011dGFibGUgYW5kXG5cdC8vIHJlYXNzaWdubWVudCBzaXRlcyAoZGVjaXNpb24gNikuIFJ1bnMgYWZ0ZXIgZGVmaW5pdGlvbnMgYXJlIGtub3duIHNvXG5cdC8vIHZhcmlhYmxlIHR5cGVQYXRocyBjYW4gcmVzb2x2ZTsgaG9sZGVyU2NvcGVJZCBpcyBhdHRhY2hlZCB0byB1c2FnZXNcblx0Ly8gYmVmb3JlIHRoZXkgYXJlIHdyaXR0ZW4uXG5cdGNvbnN0IHNjb3BlV2Fsa2VyID0gbmV3IExvY2FsU2NvcGVXYWxrZXIoKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0c2NvcGVXYWxrZXIuYWRkRmlsZShzb3VyY2VGaWxlKTtcblx0fVxuXHRjb25zdCBzY29wZVJlc29sdmVyOiBTY29wZVR5cGVSZXNvbHZlciA9IHtcblx0XHRyZXNvbHZlQnlOYW1lIDogKG5hbWU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCA9PiB7XG5cdFx0XHRpZiAoZGVmaW5pdGlvbnMuaGFzKG5hbWUpKSB7XG5cdFx0XHRcdHJldHVybiBuYW1lO1xuXHRcdFx0fVxuXHRcdFx0bGV0IGZvdW5kOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHRmb3IgKGNvbnN0IFsgZnVsbFBhdGgsIGRlZmluaXRpb24gXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdFx0XHRpZiAoZGVmaW5pdGlvbi5uYW1lICE9PSBuYW1lKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0Ly8gQW1iaWd1b3VzIG5hbWUg4oCUIG5vIHR5cGUgY2hlY2tlciwgc28gcmVmdXNlIHRvIGd1ZXNzXG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRmb3VuZCA9IGZ1bGxQYXRoO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdH0sXG5cdFx0aGFzUGF0aCA6IChmdWxsUGF0aDogc3RyaW5nKTogYm9vbGVhbiA9PiB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBkZWZpbml0aW9ucy5oYXMoZnVsbFBhdGgpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9LFxuXHRcdC8vIFRoZSBhbmFseXplcidzIG93biBsb29rdXAgbGF3LCBhZ2FpbnN0IHRoZSBzYW1lIGNvbXBsZXRlIGdyYXBoIHRoZVxuXHRcdC8vIHVzYWdlcyBwYXNzIHJlc29sdmVkIHdpdGgg4oCUIGEgbG9va3VwKCkgaW5pdGlhbGl6ZXIgdGhlIGFuYWx5emVyXG5cdFx0Ly8gYWNjZXB0ZWQgKGUuZy4gYW4gaW1wb3J0ZWQgSG9sZGVyLmxvb2t1cCgnVG9rZW4nKSkgbGFuZHMgdGhlIHNhbWVcblx0XHQvLyBmdWxsUGF0aCBpbiBzY29wZXMuanNvbiBpbnN0ZWFkIG9mIHN0YXJ2aW5nIHRoZSBjcmVhdGlvbi1ncmFwaFxuXHRcdC8vIGFuY2hvcnMuIFJlamVjdGVkIGxvb2t1cHMgc3RheSB0eXBlUGF0aC1sZXNzIGhlcmU7IHRoZSBhbmFseXplclxuXHRcdC8vIGFscmVhZHkgaGFyZC1mYWlsZWQgdGhlIHJ1biBhYm92ZS5cblx0XHRyZXNvbHZlTG9va3VwIDogKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkID0+IHtcblx0XHRcdGNvbnN0IHJlc29sdmVkID0gYW5hbHl6ZXIucmVzb2x2ZUxvb2t1cENhbGxQYXRoKGNhbGwpO1xuXHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdH0sXG5cdH07XG5cdGNvbnN0IHNjb3BlQW5hbHlzaXMgPSBzY29wZVdhbGtlci5idWlsZChzY29wZVJlc29sdmVyKTtcblx0TG9jYWxTY29wZVdhbGtlci5hdHRhY2hIb2xkZXJTY29wZUlkcyh1c2FnZXMsIHNjb3BlV2Fsa2VyKTtcblxuXHRjb25zdCBkZWZpbml0aW9uc1BhdGggPSB3cml0ZXIud3JpdGVEZWZpbml0aW9uc0ZpbGUoZGVmaW5pdGlvbnMsIGdyYXBoKTtcblx0Y29uc3QgdXNhZ2VzUGF0aCA9IHdyaXRlci53cml0ZVVzYWdlc0ZpbGUodXNhZ2VzKTtcblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBkZWZpbml0aW9ucy5qc29uIGF0OiAke2RlZmluaXRpb25zUGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHVzYWdlcy5qc29uIGF0OiAke3VzYWdlc1BhdGh9YCk7XG5cdH1cblxuXHQvLyBEZXRlcm1pbmUgRURTIHNldHRpbmc6IGV4cGxpY2l0IGZsYWcgPiBhdXRvLWRldGVjdCBkaXZlID4gZGVmYXVsdCBvZmZcblx0bGV0IGVuYWJsZUVEUyA9IG9wdGlvbnMuZWRzO1xuXHRpZiAoZW5hYmxlRURTID09PSB1bmRlZmluZWQpIHtcblx0XHRlbmFibGVFRFMgPSBoYXNEaXZlRGVwZW5kZW5jeShwcm9qZWN0RGlyKTtcblx0fVxuXG5cdGlmIChlbmFibGVFRFMpIHtcblx0XHRjb25zdCBlZHMgPSBhbmFseXplci5nZXRFRFNVc2FnZXMoKTtcblx0XHRhdHRhY2hXcmFwSm9pbkRhdGEoZWRzLCBzY29wZVdhbGtlciwgc2NvcGVBbmFseXNpcyk7XG5cdFx0Y29uc3QgZWRzUGF0aCA9IHdyaXRlci53cml0ZUVEU0ZpbGUoZWRzKTtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGVkcy5qc29uIGF0OiAke2Vkc1BhdGh9YCk7XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIGZsb3cuanNvbiAobmF0aXZlIGluc3RhbmNlIHVzYWdlIHRyYWNraW5nKVxuXHRjb25zdCBmbG93ID0gYW5hbHl6ZXIuZ2V0Rmxvd1VzYWdlcygpO1xuXHRjb25zdCBmbG93UGF0aCA9IHdyaXRlci53cml0ZUZsb3dGaWxlKGZsb3cpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3QgZmxvd0NvdW50ID0gQXJyYXkuZnJvbShmbG93LnZhbHVlcygpKS5yZWR1Y2UoKHN1bSwgYXJyKSA9PiBzdW0gKyBhcnIubGVuZ3RoLCAwKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGZsb3cuanNvbiBhdDogJHtmbG93UGF0aH0gKCR7Zmxvd0NvdW50fSBmbG93IGVudHJpZXMpYCk7XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgbW9kdWxlcy5qc29uIChtb2R1bGUtc2NvcGUgZ3JhcGg6IGltcG9ydHMvZXhwb3J0cyxcblx0Ly8gZGVwZW5kZW5jaWVzLCBjeWNsZXMsIGNyb3NzLW1vZHVsZSBtbmVtb25pY2EtdHlwZSBlZGdlcylcblx0Y29uc3QgZGVmaW5lZFR5cGVzQnlGaWxlID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZ1tdPigpO1xuXHRmb3IgKGNvbnN0IFsgZnVsbFBhdGgsIGRlZmluaXRpb24gXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdGNvbnN0IHsgbG9jYXRpb24gfSA9IGRlZmluaXRpb247XG5cdFx0Y29uc3QgbGFzdENvbG9uID0gbG9jYXRpb24ubGFzdEluZGV4T2YoJzonKTtcblx0XHRjb25zdCBwcmV2Q29sb24gPSBsb2NhdGlvbi5sYXN0SW5kZXhPZignOicsIGxhc3RDb2xvbiAtIDEpO1xuXHRcdGNvbnN0IGZpbGUgPSBsb2NhdGlvbi5zbGljZSgwLCBwcmV2Q29sb24pO1xuXHRcdGNvbnN0IGxpc3QgPSBkZWZpbmVkVHlwZXNCeUZpbGUuZ2V0KGZpbGUpID8/IFtdO1xuXHRcdGxpc3QucHVzaChmdWxsUGF0aCk7XG5cdFx0ZGVmaW5lZFR5cGVzQnlGaWxlLnNldChmaWxlLCBsaXN0KTtcblx0fVxuXHRjb25zdCBtb2R1bGVHcmFwaCA9IG1vZHVsZUdyYXBoQnVpbGRlci5idWlsZChkZWZpbmVkVHlwZXNCeUZpbGUpO1xuXHRjb25zdCBtb2R1bGVzUGF0aCA9IHdyaXRlci53cml0ZU1vZHVsZXNGaWxlKG1vZHVsZUdyYXBoKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IG1vZHVsZUNvdW50ID0gbW9kdWxlR3JhcGgubW9kdWxlcy5zaXplO1xuXHRcdGNvbnN0IGVkZ2VDb3VudCA9IG1vZHVsZUdyYXBoLmVkZ2VzLmxlbmd0aDtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIG1vZHVsZXMuanNvbiBhdDogJHttb2R1bGVzUGF0aH0gKCR7bW9kdWxlQ291bnR9IG1vZHVsZXMsICR7ZWRnZUNvdW50fSBlZGdlcylgKTtcblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBzY29wZXMuanNvbiAobG9jYWwtc2NvcGUgd2Fsa2VyOiBzY29wZXMsIHZhcmlhYmxlcyxcblx0Ly8gcmVhc3NpZ25tZW50IGZsb3ctdGVybWluYXRpb24gcG9pbnRzKVxuXHRjb25zdCBzY29wZXNQYXRoID0gd3JpdGVyLndyaXRlU2NvcGVzRmlsZShzY29wZUFuYWx5c2lzKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IHNjb3BlQ291bnQgPSBzY29wZUFuYWx5c2lzLnNjb3Blcy5zaXplO1xuXHRcdGNvbnN0IHZhcmlhYmxlQ291bnQgPSBzY29wZUFuYWx5c2lzLnZhcmlhYmxlcy5zaXplO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgc2NvcGVzLmpzb24gYXQ6ICR7c2NvcGVzUGF0aH0gKCR7c2NvcGVDb3VudH0gc2NvcGVzLCAke3ZhcmlhYmxlQ291bnR9IHZhcmlhYmxlcylgKTtcblx0fVxuXG5cdC8vIFRoZSBpbnNpZGUtb3V0IGNyZWF0aW9uIHdhbGsgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgUGhhc2UgMyk6IGFuY2hvcnNcblx0Ly8gYXJlIHRoZSBpbnN0YW50aWF0aW9uIHVzYWdlczsgY2FsbGVycyBhcmUgZm9sbG93ZWQgc2FtZS1maWxlIGFuZFxuXHQvLyBjcm9zcy1maWxlIChtb2R1bGUgZ3JhcGgsIGJhcnJlbHMgY2hhc2VkKSB1bnRpbCBvbmx5IHN0YXJ0ZXJzIHJlbWFpbi5cblx0Y29uc3Qgc291cmNlRmlsZXNCeVBhdGggPSBuZXcgTWFwPHN0cmluZywgdHMuU291cmNlRmlsZT4oKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0c291cmNlRmlsZXNCeVBhdGguc2V0KHBhdGgucmVzb2x2ZShzb3VyY2VGaWxlLmZpbGVOYW1lKSwgc291cmNlRmlsZSk7XG5cdH1cblx0Y29uc3QgY3JlYXRpb25HcmFwaEJ1aWxkZXIgPSBuZXcgQ3JlYXRpb25HcmFwaEJ1aWxkZXIobW9kdWxlR3JhcGgsIHNjb3BlQW5hbHlzaXMsIHNjb3BlV2Fsa2VyLCBzb3VyY2VGaWxlc0J5UGF0aCk7XG5cdGNvbnN0IGNyZWF0aW9uR3JhcGggPSBjcmVhdGlvbkdyYXBoQnVpbGRlci5idWlsZCh1c2FnZXMpO1xuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBpbnN0cnVtZW50YXRpb24uanNvbiAoZnJhbWV3b3JrIGxpZmVjeWNsZSBjcm9zc3JvYWRzXG5cdC8vIGZyb20gdGhlIGxvYWRlZCBwbHVnaW5zIOKAlCBzeW50YWN0aWMgZGV0ZWN0aW9uIG5lZWRzIG5vIGRpdmVcblx0Ly8gZGVwZW5kZW5jeSwgdW5saWtlIGVkcy5qc29uKS4gdjIgY2FycmllcyB0aGUgY3JlYXRpb24gZ3JhcGhcblx0Ly8gYWxvbmdzaWRlIHRoZSBwb2ludHMuXG5cdGNvbnN0IGluc3RydW1lbnRhdGlvbiA9IGFuYWx5emVyLmdldEluc3RydW1lbnRhdGlvblBvaW50cygpO1xuXHRjb25zdCBpbnN0cnVtZW50YXRpb25QYXRoID0gd3JpdGVyLndyaXRlSW5zdHJ1bWVudGF0aW9uRmlsZShpbnN0cnVtZW50YXRpb24sIGNyZWF0aW9uR3JhcGgpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3Qgbm9kZUNvdW50ID0gY3JlYXRpb25HcmFwaC5ub2Rlcy5sZW5ndGg7XG5cdFx0Y29uc3QgZWRnZUNvdW50ID0gY3JlYXRpb25HcmFwaC5lZGdlcy5sZW5ndGg7XG5cdFx0Y29uc3QgYW5jaG9yQ291bnQgPSBjcmVhdGlvbkdyYXBoLmFuY2hvcnMubGVuZ3RoO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaW5zdHJ1bWVudGF0aW9uLmpzb24gYXQ6ICR7aW5zdHJ1bWVudGF0aW9uUGF0aH0gKCR7aW5zdHJ1bWVudGF0aW9uLmxlbmd0aH0gcG9pbnRzKWApO1xuXHRcdGNvbnNvbGUubG9nKGAgIGNyZWF0aW9uIGdyYXBoOiAke25vZGVDb3VudH0gbm9kZXMsICR7ZWRnZUNvdW50fSBlZGdlcywgJHthbmNob3JDb3VudH0gYW5jaG9yc2ApO1xuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIGNvbnRyb2wuanNvbiAobGV0aGUgY29udHJhY3QsIGZvcm1hdCAxLjIpOiB0aGUgc2FtZVxuXHQvLyBjcmVhdGlvbiBncmFwaCBhbmQgcG9pbnRzIGFzIGluc3RydW1lbnRhdGlvbi5qc29uLCByZW5kZXJlZCB1bmRlciB0aGVcblx0Ly8gY3Jvc3MtbGFuZ3VhZ2UgYGNhbGxlcnNgL2Bwb2ludHNgIGtleXMuXG5cdGNvbnN0IGNvbnRyb2xQYXRoID0gd3JpdGVyLndyaXRlQ29udHJvbEZpbGUoaW5zdHJ1bWVudGF0aW9uLCBjcmVhdGlvbkdyYXBoKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgY29udHJvbC5qc29uIGF0OiAke2NvbnRyb2xQYXRofWApO1xuXHR9XG5cblx0Ly8gR2VuZXJhdGUgaGllcmFyY2h5Lmpzb24gKHN0cnVjdHVyZWQpIGFuZCBoaWVyYXJjaHkudHh0IChBU0NJSSB0cmVlKSBmb3IgdGhlIFRyaWVcblx0Y29uc3QgaGllcmFyY2h5Um9vdHMgPSBncmFwaC50b0hpZXJhcmNoeSgpO1xuXHRjb25zdCBoaWVyYXJjaHlKc29uUGF0aCA9IHdyaXRlci53cml0ZUhpZXJhcmNoeUZpbGUoaGllcmFyY2h5Um9vdHMpO1xuXHRjb25zdCBoaWVyYXJjaHlUZXh0ID0gcmVuZGVyVHlwZUhpZXJhcmNoeShncmFwaCk7XG5cdGNvbnN0IGhpZXJhcmNoeVR4dFBhdGggPSB3cml0ZXIud3JpdGVUbygnaGllcmFyY2h5LnR4dCcsIGhpZXJhcmNoeVRleHQpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBoaWVyYXJjaHkuanNvbiBhdDogJHtoaWVyYXJjaHlKc29uUGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGhpZXJhcmNoeS50eHQgYXQ6ICR7aGllcmFyY2h5VHh0UGF0aH1gKTtcblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBjb2xsZWN0aW9ucy5qc29uICh0aGUgY29sbGVjdGlvbiBtYW5pZmVzdDogaWRzLCBkaXNwbGF5XG5cdC8vIG5hbWVzLCBPcHRpb24tQiByZWdpc3RyeSBpbnRlcmZhY2VzLCBjYWxsIHNpdGVzIOKAlCB0aGUgaWTihpRpbnRlcmZhY2Ugam9pblxuXHQvLyBrZXkgYmV0d2VlbiB0aGUgcHJlZml4ZWQgZ3JhcGggb3V0cHV0cyBhbmQgdGhlIHR5cGVzLnRzIGFsaWFzZXMpXG5cdGNvbnN0IGNvbGxlY3Rpb25zUGF0aCA9IHdyaXRlci53cml0ZUNvbGxlY3Rpb25zRmlsZShhbmFseXplci5nZXRDb2xsZWN0aW9uc01hbmlmZXN0KCkpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBjb2xsZWN0aW9ucy5qc29uIGF0OiAke2NvbGxlY3Rpb25zUGF0aH1gKTtcblx0fVxuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHR5cGVzIGF0OiAke291dHB1dFBhdGh9YCk7XG5cdFx0Y29uc29sZS5sb2coJ01vZGU6IHR5cGVzIGZpbGUgKGRlZmF1bHQpJyk7XG5cdFx0Y29uc29sZS5sb2coYEZvdW5kICR7Z2VuZXJhdGVkVHlwZXMudHlwZXMubGVuZ3RofSB0eXBlczpgKTtcblx0XHRwcmludFR5cGVIaWVyYXJjaHkoZ3JhcGgpO1xuXHR9IGVsc2Uge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgJHtnZW5lcmF0ZWRUeXBlcy50eXBlcy5sZW5ndGh9IHR5cGVzIGF0ICR7b3B0aW9ucy5vdXRwdXREaXIgfHwgJy50YWN0aWNhJ31gKTtcblx0fVxuXG5cdHJldHVybiAwO1xufVxuXG4vKipcbiAqIFdhdGNoIG1vZGVcbiAqL1xuZnVuY3Rpb24gd2F0Y2ggKG9wdGlvbnM6IENMSU9wdGlvbnMpOiB2b2lkIHtcblx0Y29uc29sZS5sb2coJ1N0YXJ0aW5nIHdhdGNoIG1vZGUuLi4nKTtcblxuXHQvLyBJbml0aWFsIHJ1blxuXHRydW4ob3B0aW9ucyk7XG5cblx0Ly8gU2V0IHVwIGZpbGUgd2F0Y2hpbmdcblx0Y29uc3QgY2hva2lkYXIgPSByZXF1aXJlKCdjaG9raWRhcicpO1xuXHRjb25zdCB0c2NvbmZpZ1BhdGggPSBmaW5kVHNDb25maWcob3B0aW9ucy5wcm9qZWN0KTtcblxuXHRpZiAoIXRzY29uZmlnUGF0aCkge1xuXHRcdGNvbnNvbGUuZXJyb3IoJ0Vycm9yOiBDb3VsZCBub3QgZmluZCB0c2NvbmZpZy5qc29uJyk7XG5cdFx0cHJvY2Vzcy5leGl0KDEpO1xuXHR9XG5cblx0Y29uc3QgcHJvamVjdERpciA9IHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpO1xuXHRjb25zdCB3YXRjaFBhdGhzID0gb3B0aW9ucy5pbmNsdWRlIHx8IFsgJyoqLyoudHMnIF07XG5cdGNvbnN0IGlnbm9yZVBhdGhzID0gb3B0aW9ucy5leGNsdWRlIHx8IFsgJyoqLyouZC50cycsICdub2RlX21vZHVsZXMvKionLCAnLnRhY3RpY2EvKionIF07XG5cblx0Y29uc3Qgd2F0Y2hlciA9IGNob2tpZGFyLndhdGNoKHdhdGNoUGF0aHMsIHtcblx0XHRjd2QgICAgICAgIDogcHJvamVjdERpcixcblx0XHRpZ25vcmVkICAgIDogaWdub3JlUGF0aHMsXG5cdFx0cGVyc2lzdGVudCA6IHRydWUsXG5cdH0pO1xuXG5cdHdhdGNoZXIub24oJ2NoYW5nZScsIChmaWxlUGF0aDogc3RyaW5nKSA9PiB7XG5cdFx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0Y29uc29sZS5sb2coYEZpbGUgY2hhbmdlZDogJHtmaWxlUGF0aH1gKTtcblx0XHR9XG5cdFx0cnVuKG9wdGlvbnMpO1xuXHR9KTtcblxuXHR3YXRjaGVyLm9uKCdhZGQnLCAoZmlsZVBhdGg6IHN0cmluZykgPT4ge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBGaWxlIGFkZGVkOiAke2ZpbGVQYXRofWApO1xuXHRcdH1cblx0XHRydW4ob3B0aW9ucyk7XG5cdH0pO1xuXG5cdGNvbnNvbGUubG9nKCdXYXRjaGluZyBmb3IgY2hhbmdlcy4uLiAoUHJlc3MgQ3RybCtDIHRvIHN0b3ApJyk7XG59XG5cbi8qKlxuICogTWFpbiBlbnRyeSBwb2ludFxuICovXG5mdW5jdGlvbiBtYWluICgpOiB2b2lkIHtcblx0Y29uc3QgYXJncyA9IHByb2Nlc3MuYXJndi5zbGljZSgyKTtcblx0Y29uc3Qgb3B0aW9ucyA9IHBhcnNlQXJncyhhcmdzKTtcblxuXHRpZiAob3B0aW9ucy5oZWxwKSB7XG5cdFx0cHJpbnRIZWxwKCk7XG5cdFx0cHJvY2Vzcy5leGl0KDApO1xuXHR9XG5cblx0dHJ5IHtcblx0XHRpZiAob3B0aW9ucy53YXRjaCkge1xuXHRcdFx0d2F0Y2gob3B0aW9ucyk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdGNvbnN0IGNvZGUgPSBydW4ob3B0aW9ucyk7XG5cdFx0XHRpZiAoY29kZSkge1xuXHRcdFx0XHRwcm9jZXNzLmV4aXQoY29kZSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9IGNhdGNoIChlcnJvcikge1xuXHRcdGNvbnNvbGUuZXJyb3IoJ0Vycm9yOicsIGVycm9yIGluc3RhbmNlb2YgRXJyb3IgPyBlcnJvci5tZXNzYWdlIDogZXJyb3IpO1xuXHRcdHByb2Nlc3MuZXhpdCgxKTtcblx0fVxufVxuXG4vLyBSdW4gaWYgZXhlY3V0ZWQgZGlyZWN0bHlcbmlmIChyZXF1aXJlLm1haW4gPT09IG1vZHVsZSkge1xuXHRtYWluKCk7XG59XG5cbmV4cG9ydCB7XG5cdG1haW4sIHJ1biwgd2F0Y2gsIHBhcnNlQXJncyBcbn07XG4iXX0=