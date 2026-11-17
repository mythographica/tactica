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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiY2xpLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2NsaS50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiO0FBQ0EsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQWc5Qlosb0JBQUk7QUFBRSxrQkFBRztBQUFFLHNCQUFLO0FBQUUsOEJBQVM7QUE5OEI1Qix1Q0FBeUI7QUFDekIsMkNBQTZCO0FBQzdCLG1DQUF1QztBQUN2QywrQ0FBaUM7QUFDakMseUNBQStDO0FBQy9DLCtEQUEyRDtBQUMzRCwyQ0FFcUI7QUFDckIscUNBQXVDO0FBQ3ZDLGlEQUFvRDtBQUNwRCxxREFBd0Q7QUFDeEQscUNBRWtCO0FBQ2xCLG1DQUVpQjtBQTBCakI7O0dBRUc7QUFDSCxTQUFTLFNBQVMsQ0FBRSxJQUFjO0lBQ2pDLE1BQU0sT0FBTyxHQUFlLEVBQUUsQ0FBQztJQUUvQixLQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRSxDQUFDO1FBQ3RDLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBRSxDQUFDLENBQUUsQ0FBQztRQUV0QixRQUFRLEdBQUcsRUFBRSxDQUFDO1lBQ2QsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFNBQVM7Z0JBQ2IsT0FBTyxDQUFDLEtBQUssR0FBRyxJQUFJLENBQUM7Z0JBQ3JCLE1BQU07WUFDUCxLQUFLLElBQUksQ0FBQztZQUNWLEtBQUssV0FBVztnQkFDZixPQUFPLENBQUMsT0FBTyxHQUFHLElBQUksQ0FBRSxFQUFFLENBQUMsQ0FBRSxDQUFDO2dCQUM5QixNQUFNO1lBQ1AsS0FBSyxJQUFJLENBQUM7WUFDVixLQUFLLFVBQVU7Z0JBQ2QsT0FBTyxDQUFDLFNBQVMsR0FBRyxJQUFJLENBQUUsRUFBRSxDQUFDLENBQUUsQ0FBQztnQkFDaEMsTUFBTTtZQUNQLEtBQUssSUFBSSxDQUFDO1lBQ1YsS0FBSyxXQUFX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Q1osTUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUM7SUFDbkMsTUFBTSxPQUFPLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDO0lBRWhDLElBQUksT0FBTyxDQUFDLElBQUksRUFBRSxDQUFDO1FBQ2xCLFNBQVMsRUFBRSxDQUFDO1FBQ1osT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQztJQUNqQixDQUFDO0lBRUQsSUFBSSxDQUFDO1FBQ0osSUFBSSxPQUFPLENBQUMsS0FBSyxFQUFFLENBQUM7WUFDbkIsS0FBSyxDQUFDLE9BQU8sQ0FBQyxDQUFDO1FBQ2hCLENBQUM7YUFBTSxDQUFDO1lBQ1AsTUFBTSxJQUFJLEdBQUcsR0FBRyxDQUFDLE9BQU8sQ0FBQyxDQUFDO1lBQzFCLElBQUksSUFBSSxFQUFFLENBQUM7Z0JBQ1YsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztZQUNwQixDQUFDO1FBQ0YsQ0FBQztJQUNGLENBQUM7SUFBQyxPQUFPLEtBQUssRUFBRSxDQUFDO1FBQ2hCLE9BQU8sQ0FBQyxLQUFLLENBQUMsUUFBUSxFQUFFLEtBQUssWUFBWSxLQUFLLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDO1FBQ3hFLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUM7SUFDakIsQ0FBQztBQUNGLENBQUM7QUFFRCwyQkFBMkI7QUFDM0IsSUFBSSxPQUFPLENBQUMsSUFBSSxLQUFLLE1BQU0sRUFBRSxDQUFDO0lBQzdCLElBQUksRUFBRSxDQUFDO0FBQ1IsQ0FBQyIsInNvdXJjZXNDb250ZW50IjpbIiMhL3Vzci9iaW4vZW52IG5vZGVcbid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgZnMgZnJvbSAnZnMnO1xuaW1wb3J0ICogYXMgcGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCB7IGNyZWF0ZVJlcXVpcmUgfSBmcm9tICdtb2R1bGUnO1xuaW1wb3J0ICogYXMgdHMgZnJvbSAndHlwZXNjcmlwdCc7XG5pbXBvcnQgeyBNbmVtb25pY2FBbmFseXplciB9IGZyb20gJy4vYW5hbHl6ZXInO1xuaW1wb3J0IHsgVG9wb2xvZ2ljYUFuYWx5emVyIH0gZnJvbSAnLi90b3BvbG9naWNhLWFuYWx5emVyJztcbmltcG9ydCB7XG5cdFR5cGVzR2VuZXJhdG9yLCBHcmFwaFJlZmVyZW5jZVJlc29sdmVyIFxufSBmcm9tICcuL2dlbmVyYXRvcic7XG5pbXBvcnQgeyBUeXBlc1dyaXRlciB9IGZyb20gJy4vd3JpdGVyJztcbmltcG9ydCB7IE1vZHVsZUdyYXBoQnVpbGRlciB9IGZyb20gJy4vbW9kdWxlLWdyYXBoJztcbmltcG9ydCB7IENyZWF0aW9uR3JhcGhCdWlsZGVyIH0gZnJvbSAnLi9jcmVhdGlvbi1ncmFwaCc7XG5pbXBvcnQge1xuXHRMb2NhbFNjb3BlV2Fsa2VyLCBTY29wZVR5cGVSZXNvbHZlclxufSBmcm9tICcuL3Njb3Blcyc7XG5pbXBvcnQge1xuXHRyZXNvbHZlR3JhcGhUeXBlUmVmZXJlbmNlLCBUeXBlR3JhcGhJbXBsIFxufSBmcm9tICcuL2dyYXBoJztcbmltcG9ydCB7XG5cdFRhY3RpY2FDb25maWcsIFR5cGVOb2RlLCBFRFNJbmZvLCBTY29wZUFuYWx5c2lzLCBBbmFseXplRXJyb3Jcbn0gZnJvbSAnLi90eXBlcyc7XG5pbXBvcnQgeyBUYWN0aWNhUGx1Z2luIH0gZnJvbSAnLi9wbHVnaW5zJztcblxuLyoqXG4gKiBDTEkgZW50cnkgcG9pbnQgZm9yIFRhY3RpY2FcbiAqXG4gKiBSdW5zIHRoZSBhbmFseXplciBvdmVyIGEgdHNjb25maWcgcHJvamVjdCBhbmQgd3JpdGVzIC50YWN0aWNhLyBvdXRwdXRcbiAqL1xuXG5pbnRlcmZhY2UgQ0xJT3B0aW9ucyBleHRlbmRzIFRhY3RpY2FDb25maWcge1xuXHR3YXRjaD86IGJvb2xlYW47XG5cdHByb2plY3Q/OiBzdHJpbmc7XG5cdGhlbHA/OiBib29sZWFuO1xuXHQvKiogQ3VzdG9tIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXMgdG8gc2NhbiAqL1xuXHR0b3BvbG9naWNhRGlycz86IHN0cmluZ1tdO1xuXHQvKiogQWRkIC5qcyBleHRlbnNpb25zIHRvIHJlbGF0aXZlIGltcG9ydHMgZm9yIEVTTSBOb2RlTmV4dCByZXNvbHV0aW9uICovXG5cdGVzbT86IGJvb2xlYW47XG5cdC8qKiBFbmFibGUgRURTIChFeGVjdXRpb24gRGF0YSBTdG9yYWdlKSB0cmFja2luZyAqL1xuXHRlZHM/OiBib29sZWFuO1xuXHQvKiogUHJvZ3JhbW1hdGljIHBsdWdpbnM7IGNvbmZpZy1maWxlIHBsdWdpbnMgYXJlIGFwcGVuZGVkIGFmdGVyIHRoZXNlICovXG5cdHBsdWdpbnM/OiBUYWN0aWNhUGx1Z2luW107XG59XG5cbi8qKlxuICogUGFyc2UgY29tbWFuZCBsaW5lIGFyZ3VtZW50c1xuICovXG5mdW5jdGlvbiBwYXJzZUFyZ3MgKGFyZ3M6IHN0cmluZ1tdKTogQ0xJT3B0aW9ucyB7XG5cdGNvbnN0IG9wdGlvbnM6IENMSU9wdGlvbnMgPSB7fTtcblxuXHRmb3IgKGxldCBpID0gMDsgaSA8IGFyZ3MubGVuZ3RoOyBpKyspIHtcblx0XHRjb25zdCBhcmcgPSBhcmdzWyBpIF07XG5cblx0XHRzd2l0Y2ggKGFyZykge1xuXHRcdGNhc2UgJy13Jzpcblx0XHRjYXNlICctLXdhdGNoJzpcblx0XHRcdG9wdGlvbnMud2F0Y2ggPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLXAnOlxuXHRcdGNhc2UgJy0tcHJvamVjdCc6XG5cdFx0XHRvcHRpb25zLnByb2plY3QgPSBhcmdzWyArK2kgXTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy1vJzpcblx0XHRjYXNlICctLW91dHB1dCc6XG5cdFx0XHRvcHRpb25zLm91dHB1dERpciA9IGFyZ3NbICsraSBdO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLWknOlxuXHRcdGNhc2UgJy0taW5jbHVkZSc6XG5cdFx0XHRvcHRpb25zLmluY2x1ZGUgPSAob3B0aW9ucy5pbmNsdWRlIHx8IFtdKS5jb25jYXQoYXJnc1sgKytpIF0uc3BsaXQoJywnKSk7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctZSc6XG5cdFx0Y2FzZSAnLS1leGNsdWRlJzpcblx0XHRcdG9wdGlvbnMuZXhjbHVkZSA9IChvcHRpb25zLmV4Y2x1ZGUgfHwgW10pLmNvbmNhdChhcmdzWyArK2kgXS5zcGxpdCgnLCcpKTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy12Jzpcblx0XHRjYXNlICctLXZlcmJvc2UnOlxuXHRcdFx0b3B0aW9ucy52ZXJib3NlID0gdHJ1ZTtcblx0XHRcdGJyZWFrO1xuXHRcdGNhc2UgJy10Jzpcblx0XHRjYXNlICctLXRvcG9sb2dpY2EnOlxuXHRcdFx0b3B0aW9ucy50b3BvbG9naWNhRGlycyA9IChvcHRpb25zLnRvcG9sb2dpY2FEaXJzIHx8IFtdKS5jb25jYXQoYXJnc1sgKytpIF0uc3BsaXQoJywnKSk7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctLWVzbSc6XG5cdFx0XHRvcHRpb25zLmVzbSA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctLWVkcyc6XG5cdFx0XHRvcHRpb25zLmVkcyA9IHRydWU7XG5cdFx0XHRicmVhaztcblx0XHRjYXNlICctLW5vLWVkcyc6XG5cdFx0XHRvcHRpb25zLmVkcyA9IGZhbHNlO1xuXHRcdFx0YnJlYWs7XG5cdFx0Y2FzZSAnLWgnOlxuXHRcdGNhc2UgJy0taGVscCc6XG5cdFx0XHRvcHRpb25zLmhlbHAgPSB0cnVlO1xuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIG9wdGlvbnM7XG59XG5cbi8qKlxuICogUHJpbnQgaGVscCBtZXNzYWdlXG4gKi9cbmZ1bmN0aW9uIHByaW50SGVscCAoKTogdm9pZCB7XG5cdGNvbnNvbGUubG9nKGBcblRhY3RpY2EgLSBUeXBlIGRlZmluaXRpb24gZ2VuZXJhdG9yIGZvciBNbmVtb25pY2FcblxuVXNhZ2U6IHRhY3RpY2EgW29wdGlvbnNdXG5cbk9wdGlvbnM6XG4gIC13LCAtLXdhdGNoICAgICAgICAgICAgICAgV2F0Y2ggZm9yIGZpbGUgY2hhbmdlcyBhbmQgcmVnZW5lcmF0ZSB0eXBlc1xuICAtcCwgLS1wcm9qZWN0ICAgICAgICAgICAgIFBhdGggdG8gdHNjb25maWcuanNvbiAoZGVmYXVsdDogLi90c2NvbmZpZy5qc29uKVxuICAtbywgLS1vdXRwdXQgICAgICAgICAgICAgIE91dHB1dCBkaXJlY3RvcnkgZm9yIGdlbmVyYXRlZCB0eXBlcyAoZGVmYXVsdDogLnRhY3RpY2EpXG4gIC1pLCAtLWluY2x1ZGUgICAgICAgICAgICAgQ29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgZmlsZSBwYXR0ZXJucyB0byBpbmNsdWRlXG4gIC1lLCAtLWV4Y2x1ZGUgICAgICAgICAgICAgQ29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgZmlsZSBwYXR0ZXJucyB0byBleGNsdWRlXG4gIC10LCAtLXRvcG9sb2dpY2EgICAgICAgICAgQ29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgdG9wb2xvZ2ljYSBkaXJlY3RvcmllcyB0byBzY2FuXG4gIC0tZXNtICAgICAgICAgICAgICAgICAgICAgQWRkIC5qcyBleHRlbnNpb25zIHRvIHJlbGF0aXZlIGltcG9ydHMgKE5vZGVOZXh0IEVTTSlcbiAgLS1lZHMgICAgICAgICAgICAgICAgICAgICBFbmFibGUgRURTIChFeGVjdXRpb24gRGF0YSBTdG9yYWdlKSB0cmFja2luZ1xuICAtLW5vLWVkcyAgICAgICAgICAgICAgICAgIERpc2FibGUgRURTIHRyYWNraW5nXG4gIC12LCAtLXZlcmJvc2UgICAgICAgICAgICAgRW5hYmxlIHZlcmJvc2UgbG9nZ2luZ1xuICAtaCwgLS1oZWxwICAgICAgICAgICAgICAgIFNob3cgdGhpcyBoZWxwIG1lc3NhZ2VcblxuQ29uZmlndXJhdGlvbjpcbiAgRnJhbWV3b3JrIGluc3RydW1lbnRhdGlvbiB2b2NhYnVsYXJ5IGlzIHN1cHBsaWVkIGJ5IHBsdWdpbnMuIFBsYWNlIGFcbiAgLnRhY3RpY2EuanMgKG9yIHRhY3RpY2EuY29uZmlnLmpzKSBuZXh0IHRvIHlvdXIgdHNjb25maWcuanNvbjpcblxuICAgICAgbW9kdWxlLmV4cG9ydHMgPSB7IHBsdWdpbnM6IFsgJ3lvdXItZnJhbWV3b3JrLWFkYXB0ZXIvdGFjdGljYScgXSB9O1xuXG4gIEVudHJpZXMgYXJlIG1vZHVsZSBzcGVjaWZpZXJzIChyZXF1aXJlZCByZWxhdGl2ZSB0byB0aGUgY29uZmlnIGZpbGUpIG9yXG4gIGlubGluZSBwbHVnaW4gb2JqZWN0cy4gV2l0aG91dCBwbHVnaW5zLCBpbnN0cnVtZW50YXRpb24uanNvbiBwb2ludHMgPSBbXS5cblxuRXhhbXBsZXM6XG4gIHRhY3RpY2EgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAjIEdlbmVyYXRlIHR5cGVzLnRzIGFuZCByZWdpc3RyeS50c1xuICB0YWN0aWNhIC0td2F0Y2ggICAgICAgICAgICAgICAgICAgICAgIyBXYXRjaCBtb2RlXG4gIHRhY3RpY2EgLS1wcm9qZWN0IC4vc3JjL3RzY29uZmlnLmpzb24gIyBDdXN0b20gdHNjb25maWcgcGF0aFxuICB0YWN0aWNhIC0tb3V0cHV0IC4vdHlwZXMvbW5lbW9uaWNhICAgIyBDdXN0b20gb3V0cHV0IGRpcmVjdG9yeVxuICB0YWN0aWNhIC0tdG9wb2xvZ2ljYSAuL3NyYy9haS10eXBlcyAgIyBTY2FuIHNwZWNpZmljIHRvcG9sb2dpY2EgZGlyZWN0b3J5XG5gKTtcbn1cblxuLyoqXG4gKiBGaW5kIHRzY29uZmlnLmpzb25cbiAqL1xuZnVuY3Rpb24gZmluZFRzQ29uZmlnIChwcm9qZWN0UGF0aD86IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdGlmIChwcm9qZWN0UGF0aCkge1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKHByb2plY3RQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHByb2plY3RQYXRoO1xuXHRcdH1cblx0XHR0aHJvdyBuZXcgRXJyb3IoYFByb2plY3QgZmlsZSBub3QgZm91bmQ6ICR7cHJvamVjdFBhdGh9YCk7XG5cdH1cblxuXHQvLyBMb29rIGZvciB0c2NvbmZpZy5qc29uIGluIGN1cnJlbnQgZGlyZWN0b3J5IGFuZCBwYXJlbnQgZGlyZWN0b3JpZXNcblx0bGV0IGN1cnJlbnREaXIgPSBwcm9jZXNzLmN3ZCgpO1xuXHR3aGlsZSAoY3VycmVudERpciAhPT0gcGF0aC5kaXJuYW1lKGN1cnJlbnREaXIpKSB7XG5cdFx0Y29uc3QgdHNjb25maWdQYXRoID0gcGF0aC5qb2luKGN1cnJlbnREaXIsICd0c2NvbmZpZy5qc29uJyk7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmModHNjb25maWdQYXRoKSkge1xuXHRcdFx0cmV0dXJuIHRzY29uZmlnUGF0aDtcblx0XHR9XG5cdFx0Y3VycmVudERpciA9IHBhdGguZGlybmFtZShjdXJyZW50RGlyKTtcblx0fVxuXG5cdHJldHVybiB1bmRlZmluZWQ7XG59XG5cbi8qKlxuICogTG9hZCBUeXBlU2NyaXB0IHByb2dyYW0gZnJvbSB0c2NvbmZpZ1xuICovXG5mdW5jdGlvbiBsb2FkUHJvZ3JhbSAodHNjb25maWdQYXRoOiBzdHJpbmcpOiB0cy5Qcm9ncmFtIHtcblx0Y29uc3QgY29uZmlnRmlsZSA9IHRzLnJlYWRDb25maWdGaWxlKHRzY29uZmlnUGF0aCwgdHMuc3lzLnJlYWRGaWxlKTtcblxuXHRpZiAoY29uZmlnRmlsZS5lcnJvcikge1xuXHRcdGNvbnN0IGVycm9yVGV4dCA9IHRzLmZsYXR0ZW5EaWFnbm9zdGljTWVzc2FnZVRleHQoXG5cdFx0XHRjb25maWdGaWxlLmVycm9yLm1lc3NhZ2VUZXh0LFxuXHRcdFx0J1xcbidcblx0XHQpO1xuXHRcdHRocm93IG5ldyBFcnJvcihgRXJyb3IgcmVhZGluZyB0c2NvbmZpZzogJHtlcnJvclRleHR9YCk7XG5cdH1cblxuXHQvLyBUYWN0aWNhIGFuYWx5emVzIHdpdGggaXRzIG93biBidW5kbGVkIFR5cGVTY3JpcHQsIHdoaWNoIG1heSBiZSBuZXdlclxuXHQvLyB0aGFuIHRoZSBjb21waWxlciB0aGUgdXNlcidzIHRzY29uZmlnIHdhcyB3cml0dGVuIGZvciAoZS5nLiBhIFRTNS1lcmFcblx0Ly8gY29uZmlnIGNhcnJ5aW5nIGBiYXNlVXJsYCwgZGVwcmVjYXRlZC1lcnJvcmVkIGJ5IFRTNidzIFRTNTEwMSkuXG5cdC8vIEFuYWx5c2lzIG5ldmVyIGVtaXRzIHVzZXIgY29kZSwgc28gZGVwcmVjYXRpb24gZXJyb3JzIGFyZSBhYm91dCB0aGVcblx0Ly8gdXNlcidzIGJ1aWxkIHBpcGVsaW5lLCBub3QgYWJvdXQgYW5hbHl6YWJpbGl0eSDigJQgc2lsZW5jZSB0aGVtIGZvciB0aGVcblx0Ly8gYW5hbHlzaXMgcHJvZ3JhbS4gVW5jb25kaXRpb25hbDogYSB1c2VyLXBpbm5lZCBvbGRlciB2YWx1ZSAoJzUuMCcpXG5cdC8vIGRvZXMgbm90IHNpbGVuY2UgNi4wIGRlcHJlY2F0aW9ucyBhbmQgd291bGQgc3RpbGwgZmF0YWwgYmVsb3cuXG5cdGNvbnN0IHJhd0NvbmZpZyA9IGNvbmZpZ0ZpbGUuY29uZmlnID8/IHt9O1xuXHRyYXdDb25maWcuY29tcGlsZXJPcHRpb25zID0ge1xuXHRcdC4uLnJhd0NvbmZpZy5jb21waWxlck9wdGlvbnMsXG5cdFx0aWdub3JlRGVwcmVjYXRpb25zIDogJzYuMCcsXG5cdH07XG5cblx0Y29uc3QgcGFyc2VkQ29uZmlnID0gdHMucGFyc2VKc29uQ29uZmlnRmlsZUNvbnRlbnQoXG5cdFx0cmF3Q29uZmlnLFxuXHRcdHRzLnN5cyxcblx0XHRwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKVxuXHQpO1xuXG5cdGlmIChwYXJzZWRDb25maWcuZXJyb3JzLmxlbmd0aCA+IDApIHtcblx0XHRjb25zdCBlcnJvck1lc3NhZ2VzID0gcGFyc2VkQ29uZmlnLmVycm9ycy5tYXAoZSA9PlxuXHRcdFx0dHMuZmxhdHRlbkRpYWdub3N0aWNNZXNzYWdlVGV4dChlLm1lc3NhZ2VUZXh0LCAnXFxuJykpO1xuXHRcdHRocm93IG5ldyBFcnJvcihgRXJyb3IgcGFyc2luZyB0c2NvbmZpZzogJHtlcnJvck1lc3NhZ2VzLmpvaW4oJ1xcbicpfWApO1xuXHR9XG5cblx0Y29uc3QgcHJvZ3JhbSA9IHRzLmNyZWF0ZVByb2dyYW0oe1xuXHRcdHJvb3ROYW1lcyA6IHBhcnNlZENvbmZpZy5maWxlTmFtZXMsXG5cdFx0b3B0aW9ucyAgIDogcGFyc2VkQ29uZmlnLm9wdGlvbnMsXG5cdH0pO1xuXG5cdHJldHVybiBwcm9ncmFtO1xufVxuXG4vKipcbiAqIExvb2sgdXAgYSB2YXJpYWJsZSBieSBuYW1lIHN0YXJ0aW5nIGZyb20gYSBzY29wZSwgd2Fsa2luZyBvdXR3YXJkIHRocm91Z2hcbiAqIHBhcmVudFNjb3BlSWQuIFRoZSBpbm5lcm1vc3QgYmluZGluZyB3aW5zIGV2ZW4gd2hlbiBpdCBjYXJyaWVzIG5vIHR5cGVQYXRoXG4gKiAoc2hhZG93aW5nIGhvbmVzdHkg4oCUIGFuIHVudHlwZWQgbG9jYWwgc2hhZG93cyBhIHR5cGVkIG91dGVyIG9uZSkuXG4gKi9cbmZ1bmN0aW9uIHJlc29sdmVTY29wZWRWYXJpYWJsZVR5cGVQYXRoIChcblx0bmFtZTogc3RyaW5nLFxuXHRzY29wZUlkOiBzdHJpbmcsXG5cdHNjb3BlQW5hbHlzaXM6IFNjb3BlQW5hbHlzaXNcbik6IHN0cmluZyB8IHVuZGVmaW5lZCB7XG5cdGxldCBjdXJyZW50OiBzdHJpbmcgfCB1bmRlZmluZWQgPSBzY29wZUlkO1xuXHR3aGlsZSAoY3VycmVudCkge1xuXHRcdGNvbnN0IHZhcmlhYmxlID0gc2NvcGVBbmFseXNpcy52YXJpYWJsZXMuZ2V0KGAke2N1cnJlbnR9IyR7bmFtZX1gKTtcblx0XHRpZiAodmFyaWFibGUpIHtcblx0XHRcdGNvbnN0IHsgdHlwZVBhdGggfSA9IHZhcmlhYmxlO1xuXHRcdFx0cmV0dXJuIHR5cGVQYXRoO1xuXHRcdH1cblx0XHRjdXJyZW50ID0gc2NvcGVBbmFseXNpcy5zY29wZXMuZ2V0KGN1cnJlbnQpPy5wYXJlbnRTY29wZUlkO1xuXHR9XG5cdHJldHVybiB1bmRlZmluZWQ7XG59XG5cbi8qKlxuICogSm9pbiBkYXRhIGZvciBtbmVtb2dyYXBoaWNhJ3Mgd3JhcHBlcnMgbGF5ZXI6IHBpbiBlYWNoIHdyYXAgZW50cnkgdG8gdGhlXG4gKiBzY29wZSBob2xkaW5nIGl0cyBjYWxsIHNpdGUsIGFuZCByZXNvbHZlIHRoZSB3cmFwcGVkIGluc3RhbmNlIGFyZ3VtZW50J3NcbiAqIG1uZW1vbmljYSB0eXBlIHRocm91Z2ggdGhlIHNjb3BlLXZhcmlhYmxlIGNoYWluLlxuICovXG5mdW5jdGlvbiBhdHRhY2hXcmFwSm9pbkRhdGEgKFxuXHRlZHM6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4sXG5cdHNjb3BlV2Fsa2VyOiBMb2NhbFNjb3BlV2Fsa2VyLFxuXHRzY29wZUFuYWx5c2lzOiBTY29wZUFuYWx5c2lzXG4pOiB2b2lkIHtcblx0Zm9yIChjb25zdCBlbnRyaWVzIG9mIGVkcy52YWx1ZXMoKSkge1xuXHRcdGZvciAoY29uc3QgZW50cnkgb2YgZW50cmllcykge1xuXHRcdFx0aWYgKGVudHJ5LmtpbmQgIT09ICd3cmFwJykge1xuXHRcdFx0XHRjb250aW51ZTtcblx0XHRcdH1cblx0XHRcdGNvbnN0IGhvbGRlclNjb3BlSWQgPSBzY29wZVdhbGtlci5maW5kSG9sZGVyU2NvcGVJZChlbnRyeS5sb2NhdGlvbik7XG5cdFx0XHRpZiAoIWhvbGRlclNjb3BlSWQpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRlbnRyeS5zY29wZUlkID0gaG9sZGVyU2NvcGVJZDtcblx0XHRcdGlmICghZW50cnkuaW5zdGFuY2VBcmcpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCB3cmFwc1R5cGVQYXRoID0gcmVzb2x2ZVNjb3BlZFZhcmlhYmxlVHlwZVBhdGgoXG5cdFx0XHRcdGVudHJ5Lmluc3RhbmNlQXJnLFxuXHRcdFx0XHRob2xkZXJTY29wZUlkLFxuXHRcdFx0XHRzY29wZUFuYWx5c2lzXG5cdFx0XHQpO1xuXHRcdFx0aWYgKHdyYXBzVHlwZVBhdGgpIHtcblx0XHRcdFx0ZW50cnkud3JhcHNUeXBlUGF0aCA9IHdyYXBzVHlwZVBhdGg7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG59XG5cbi8qKlxuICogUmVuZGVyIHR5cGUgaGllcmFyY2h5IGFzIGFuIEFTQ0lJIHRyZWUgc3RyaW5nLlxuICogRGlzcGxheS1vbmx5OiBzaWJsaW5ncyBhcmUgc29ydGVkIGJ5IGZ1bGxQYXRoIGF0IHJlbmRlciB0aW1lIChjb2RlLXVuaXRcbiAqIG9yZGVyIOKAlCBkZWZhdWx0LWNvbGxlY3Rpb24gUGFzY2FsQ2FzZSByb290cyBsYW5kIGJlZm9yZSB0aGVcbiAqIGBjb2xsZWN0aW9uX046OmAtcHJlZml4ZWQgb25lcykuIFRoZSBncmFwaCBpdHNlbGYga2VlcHMgZGlzY292ZXJ5IG9yZGVyO1xuICogaGllcmFyY2h5Lmpzb24gaXMgdW5hZmZlY3RlZC5cbiAqL1xuZnVuY3Rpb24gcmVuZGVyVHlwZUhpZXJhcmNoeSAoZ3JhcGg6IFR5cGVHcmFwaEltcGwpOiBzdHJpbmcge1xuXHRjb25zdCBsaW5lczogc3RyaW5nW10gPSBbICdUeXBlIEhpZXJhcmNoeSAoVHJpZSk6JyBdO1xuXG5cdGZ1bmN0aW9uIHNvcnRlZEJ5RnVsbFBhdGggKG5vZGVzOiBUeXBlTm9kZVtdKTogVHlwZU5vZGVbXSB7XG5cdFx0Y29uc3Qgc29ydGVkID0gQXJyYXkuZnJvbShub2Rlcyk7XG5cdFx0c29ydGVkLnNvcnQoKGEsIGIpID0+IHtcblx0XHRcdGlmIChhLmZ1bGxQYXRoIDwgYi5mdWxsUGF0aCkgeyByZXR1cm4gLTE7IH1cblx0XHRcdGlmIChhLmZ1bGxQYXRoID4gYi5mdWxsUGF0aCkgeyByZXR1cm4gMTsgfVxuXHRcdFx0cmV0dXJuIDA7XG5cdFx0fSk7XG5cdFx0cmV0dXJuIHNvcnRlZDtcblx0fVxuXG5cdGZ1bmN0aW9uIHJlbmRlck5vZGUgKG5vZGU6IFR5cGVOb2RlLCBwcmVmaXggPSAnJywgaXNMYXN0ID0gdHJ1ZSk6IHZvaWQge1xuXHRcdGNvbnN0IGNvbm5lY3RvciA9IGlzTGFzdCA/ICfilJTilIDilIAgJyA6ICfilJzilIDilIAgJztcblx0XHQvLyBVc2Ugbm9kZS5mdWxsUGF0aCBkaXJlY3RseSBhbmQgY29udmVydCBkb3RzIHRvIHVuZGVyc2NvcmVzXG5cdFx0Y29uc3QgaW5zdGFuY2VOYW1lID0gbm9kZS5mdWxsUGF0aC5yZXBsYWNlKC9cXC4vZywgJ18nKTtcblx0XHRsaW5lcy5wdXNoKGAke3ByZWZpeH0ke2Nvbm5lY3Rvcn0ke2luc3RhbmNlTmFtZX1gKTtcblxuXHRcdGNvbnN0IGNoaWxkcmVuID0gc29ydGVkQnlGdWxsUGF0aChBcnJheS5mcm9tKG5vZGUuY2hpbGRyZW4udmFsdWVzKCkpKTtcblx0XHRjb25zdCBuZXdQcmVmaXggPSBwcmVmaXggKyAoaXNMYXN0ID8gJyAgICAnIDogJ+KUgiAgICcpO1xuXG5cdFx0Zm9yIChsZXQgaSA9IDA7IGkgPCBjaGlsZHJlbi5sZW5ndGg7IGkrKykge1xuXHRcdFx0cmVuZGVyTm9kZShjaGlsZHJlblsgaSBdLCBuZXdQcmVmaXgsIGkgPT09IGNoaWxkcmVuLmxlbmd0aCAtIDEpO1xuXHRcdH1cblx0fVxuXG5cdGNvbnN0IHJvb3RzID0gc29ydGVkQnlGdWxsUGF0aChBcnJheS5mcm9tKGdyYXBoLnJvb3RzLnZhbHVlcygpKSk7XG5cdGZvciAobGV0IGkgPSAwOyBpIDwgcm9vdHMubGVuZ3RoOyBpKyspIHtcblx0XHRyZW5kZXJOb2RlKHJvb3RzWyBpIF0sICcnLCBpID09PSByb290cy5sZW5ndGggLSAxKTtcblx0fVxuXHQvLyBFbXB0eSBsaW5lIGF0IGVuZFxuXHRsaW5lcy5wdXNoKCcnKTtcblxuXHRjb25zdCByZXN1bHQgPSBsaW5lcy5qb2luKCdcXG4nKTtcblx0cmV0dXJuIHJlc3VsdDtcbn1cblxuLyoqXG4gKiBQcmludCB0eXBlIGhpZXJhcmNoeSB0byB0aGUgY29uc29sZS5cbiAqL1xuZnVuY3Rpb24gcHJpbnRUeXBlSGllcmFyY2h5IChncmFwaDogVHlwZUdyYXBoSW1wbCk6IHZvaWQge1xuXHRjb25zdCBvdXRwdXQgPSByZW5kZXJUeXBlSGllcmFyY2h5KGdyYXBoKTtcblx0Y29uc29sZS5sb2cob3V0cHV0KTtcbn1cblxuLyoqXG4gKiBDaGVjayBpZiBAbW5lbW9uaWNhL2RpdmUgaXMgcHJlc2VudCBpbiBwYWNrYWdlLmpzb24gZGVwZW5kZW5jaWVzXG4gKi9cbmZ1bmN0aW9uIGhhc0RpdmVEZXBlbmRlbmN5IChwcm9qZWN0RGlyOiBzdHJpbmcpOiBib29sZWFuIHtcblx0Y29uc3QgcGFja2FnZUpzb25QYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsICdwYWNrYWdlLmpzb24nKTtcblx0aWYgKCFmcy5leGlzdHNTeW5jKHBhY2thZ2VKc29uUGF0aCkpIHtcblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cblx0dHJ5IHtcblx0XHRjb25zdCBjb250ZW50ID0gZnMucmVhZEZpbGVTeW5jKHBhY2thZ2VKc29uUGF0aCwgJ3V0Zi04Jyk7XG5cdFx0Y29uc3QgcGtnID0gSlNPTi5wYXJzZShjb250ZW50KTtcblx0XHRjb25zdCBkZXBzID0gcGtnLmRlcGVuZGVuY2llcyB8fCB7fTtcblx0XHRjb25zdCBkZXZEZXBzID0gcGtnLmRldkRlcGVuZGVuY2llcyB8fCB7fTtcblx0XHRjb25zdCBwZWVyRGVwcyA9IHBrZy5wZWVyRGVwZW5kZW5jaWVzIHx8IHt9O1xuXHRcdHJldHVybiAnQG1uZW1vbmljYS9kaXZlJyBpbiBkZXBzIHx8ICdAbW5lbW9uaWNhL2RpdmUnIGluIGRldkRlcHMgfHwgJ0BtbmVtb25pY2EvZGl2ZScgaW4gcGVlckRlcHM7XG5cdH0gY2F0Y2gge1xuXHRcdHJldHVybiBmYWxzZTtcblx0fVxufVxuXG4vKipcbiAqIFNjYW4gZm9yIHRvcG9sb2dpY2EgZGlyZWN0b3J5IHN0cnVjdHVyZXNcbiAqL1xuZnVuY3Rpb24gc2NhblRvcG9sb2dpY2FEaXJlY3RvcmllcyAocHJvamVjdERpcjogc3RyaW5nLCBjdXN0b21EaXJzPzogc3RyaW5nW10pOiBzdHJpbmdbXSB7XG5cdGNvbnN0IGRpcnM6IHN0cmluZ1tdID0gW107XG5cblx0Ly8gRmlyc3QsIGFkZCBjdXN0b20gZGlyZWN0b3JpZXMgaWYgc3BlY2lmaWVkXG5cdGlmIChjdXN0b21EaXJzKSB7XG5cdFx0Zm9yIChjb25zdCBkaXIgb2YgY3VzdG9tRGlycykge1xuXHRcdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguaXNBYnNvbHV0ZShkaXIpID8gZGlyIDogcGF0aC5qb2luKHByb2plY3REaXIsIGRpcik7XG5cdFx0XHRpZiAoZnMuZXhpc3RzU3luYyhkaXJQYXRoKSAmJiBmcy5zdGF0U3luYyhkaXJQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHRcdGRpcnMucHVzaChkaXJQYXRoKTtcblx0XHRcdH0gZWxzZSB7XG5cdFx0XHRcdGNvbnNvbGUud2FybihgV2FybmluZzogVG9wb2xvZ2ljYSBkaXJlY3Rvcnkgbm90IGZvdW5kOiAke2RpclBhdGh9YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0Ly8gVGhlbiBhdXRvLWRpc2NvdmVyIHN0YW5kYXJkIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXNcblx0Y29uc3QgcG9zc2libGVEaXJzID0gWyAnYWktdHlwZXMnLCAndHlwZXMnLCAndG9wb2xvZ2ljYS10eXBlcycgXTtcblxuXHRmb3IgKGNvbnN0IGRpck5hbWUgb2YgcG9zc2libGVEaXJzKSB7XG5cdFx0Y29uc3QgZGlyUGF0aCA9IHBhdGguam9pbihwcm9qZWN0RGlyLCBkaXJOYW1lKTtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyhkaXJQYXRoKSAmJiBmcy5zdGF0U3luYyhkaXJQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHQvLyBBdm9pZCBkdXBsaWNhdGVzXG5cdFx0XHRpZiAoIWRpcnMuaW5jbHVkZXMoZGlyUGF0aCkpIHtcblx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8vIEFsc28gc2NhbiBzcmMvIHN1YmRpcmVjdG9yeVxuXHRjb25zdCBzcmNQYXRoID0gcGF0aC5qb2luKHByb2plY3REaXIsICdzcmMnKTtcblx0aWYgKGZzLmV4aXN0c1N5bmMoc3JjUGF0aCkgJiYgZnMuc3RhdFN5bmMoc3JjUGF0aCkuaXNEaXJlY3RvcnkoKSkge1xuXHRcdGZvciAoY29uc3QgZGlyTmFtZSBvZiBwb3NzaWJsZURpcnMpIHtcblx0XHRcdGNvbnN0IGRpclBhdGggPSBwYXRoLmpvaW4oc3JjUGF0aCwgZGlyTmFtZSk7XG5cdFx0XHRpZiAoZnMuZXhpc3RzU3luYyhkaXJQYXRoKSAmJiBmcy5zdGF0U3luYyhkaXJQYXRoKS5pc0RpcmVjdG9yeSgpKSB7XG5cdFx0XHRcdC8vIEF2b2lkIGR1cGxpY2F0ZXNcblx0XHRcdFx0aWYgKCFkaXJzLmluY2x1ZGVzKGRpclBhdGgpKSB7XG5cdFx0XHRcdFx0ZGlycy5wdXNoKGRpclBhdGgpO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIGRpcnM7XG59XG5cbi8qKlxuICogQ29uZmlnIGZpbGUgY2FuZGlkYXRlcyAoZXNsaW50LXN0eWxlIHByb2plY3QgY29uZmlnKSwgc2VhcmNoZWQgbmV4dCB0b1xuICogdGhlIHJlc29sdmVkIHRzY29uZmlnIGZpcnN0LCB0aGVuIGluIHRoZSBjdXJyZW50IHdvcmtpbmcgZGlyZWN0b3J5LlxuICovXG5jb25zdCBDT05GSUdfRklMRV9OQU1FUyA9IFsgJy50YWN0aWNhLmpzJywgJ3RhY3RpY2EuY29uZmlnLmpzJyBdO1xuXG5pbnRlcmZhY2UgVGFjdGljYUNvbmZpZ0ZpbGUge1xuXHRwbHVnaW5zPzogQXJyYXk8VGFjdGljYVBsdWdpbiB8IHN0cmluZz47XG59XG5cbi8qKlxuICogTG9hZCBmcmFtZXdvcmstdm9jYWJ1bGFyeSBwbHVnaW5zOiBwcm9ncmFtbWF0aWMgb3B0aW9ucyBmaXJzdCwgdGhlbiB0aGVcbiAqIHByb2plY3QgY29uZmlnIGZpbGUuIFN0cmluZyBlbnRyaWVzIGFyZSBtb2R1bGUgc3BlY2lmaWVycyByZXF1aXJlZFxuICogcmVsYXRpdmUgdG8gdGhlIGNvbmZpZyBmaWxlIChlLmcuIGFuIGFkYXB0ZXIgcGFja2FnZSdzIHBsdWdpbiBzdWJwYXRoKS5cbiAqIFdpdGhvdXQgYSBjb25maWcgZmlsZSBhbmQgd2l0aG91dCBwcm9ncmFtbWF0aWMgcGx1Z2lucyB0aGUgYW5hbHl6ZXJcbiAqIHN0YXlzIGZyYW1ld29yay1ibGluZCBhbmQgaW5zdHJ1bWVudGF0aW9uLmpzb24gY2FycmllcyBlbXB0eSBwb2ludHMuXG4gKi9cbmZ1bmN0aW9uIGxvYWRUYWN0aWNhUGx1Z2lucyAocHJvamVjdERpcjogc3RyaW5nLCBvcHRpb25zOiBDTElPcHRpb25zKTogVGFjdGljYVBsdWdpbltdIHtcblx0Y29uc3QgcGx1Z2luczogVGFjdGljYVBsdWdpbltdID0gWyAuLi4ob3B0aW9ucy5wbHVnaW5zIHx8IFtdKSBdO1xuXG5cdGNvbnN0IHNlYXJjaERpcnMgPSBbIHByb2plY3REaXIgXTtcblx0Y29uc3QgY3dkID0gcHJvY2Vzcy5jd2QoKTtcblx0aWYgKGN3ZCAhPT0gcHJvamVjdERpcikge1xuXHRcdHNlYXJjaERpcnMucHVzaChjd2QpO1xuXHR9XG5cblx0bGV0IGNvbmZpZ1BhdGg6IHN0cmluZyB8IHVuZGVmaW5lZDtcblx0Zm9yIChjb25zdCBkaXIgb2Ygc2VhcmNoRGlycykge1xuXHRcdGZvciAoY29uc3QgbmFtZSBvZiBDT05GSUdfRklMRV9OQU1FUykge1xuXHRcdFx0Y29uc3QgY2FuZGlkYXRlID0gcGF0aC5qb2luKGRpciwgbmFtZSk7XG5cdFx0XHRpZiAoZnMuZXhpc3RzU3luYyhjYW5kaWRhdGUpKSB7XG5cdFx0XHRcdGNvbmZpZ1BhdGggPSBjYW5kaWRhdGU7XG5cdFx0XHRcdGJyZWFrO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAoY29uZmlnUGF0aCkge1xuXHRcdFx0YnJlYWs7XG5cdFx0fVxuXHR9XG5cblx0aWYgKCFjb25maWdQYXRoKSB7XG5cdFx0cmV0dXJuIHBsdWdpbnM7XG5cdH1cblxuXHQvLyBjcmVhdGVSZXF1aXJlIGFuY2hvcmVkIGF0IHRoZSBjb25maWcgZmlsZTogdGhlIGNvbmZpZydzIG93biBpbXBvcnRzXG5cdC8vIGFuZCBzdHJpbmcgcGx1Z2luIHNwZWNpZmllcnMgcmVzb2x2ZSBhZ2FpbnN0IHRoZSBwcm9qZWN0J3MgbW9kdWxlc1xuXHRjb25zdCBjb25maWdSZXF1aXJlID0gY3JlYXRlUmVxdWlyZShjb25maWdQYXRoKTtcblx0Y29uc3QgbG9hZGVkID0gY29uZmlnUmVxdWlyZShjb25maWdQYXRoKTtcblx0Y29uc3QgY29uZmlnOiBUYWN0aWNhQ29uZmlnRmlsZSA9IGxvYWRlZCAmJiB0eXBlb2YgbG9hZGVkID09PSAnb2JqZWN0JyAmJiAnZGVmYXVsdCcgaW4gbG9hZGVkXG5cdFx0PyBsb2FkZWQuZGVmYXVsdFxuXHRcdDogbG9hZGVkO1xuXHRjb25zdCBlbnRyaWVzID0gY29uZmlnICYmIEFycmF5LmlzQXJyYXkoY29uZmlnLnBsdWdpbnMpID8gY29uZmlnLnBsdWdpbnMgOiBbXTtcblxuXHRmb3IgKGNvbnN0IGVudHJ5IG9mIGVudHJpZXMpIHtcblx0XHRpZiAodHlwZW9mIGVudHJ5ICE9PSAnc3RyaW5nJykge1xuXHRcdFx0cGx1Z2lucy5wdXNoKGVudHJ5KTtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblx0XHRjb25zdCBtb2QgPSBjb25maWdSZXF1aXJlKGVudHJ5KTtcblx0XHRjb25zdCBwbHVnaW46IFRhY3RpY2FQbHVnaW4gPSBtb2QgJiYgdHlwZW9mIG1vZCA9PT0gJ29iamVjdCcgJiYgJ2RlZmF1bHQnIGluIG1vZFxuXHRcdFx0PyBtb2QuZGVmYXVsdFxuXHRcdFx0OiBtb2Q7XG5cdFx0cGx1Z2lucy5wdXNoKHBsdWdpbik7XG5cdH1cblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3QgbmFtZXMgPSBwbHVnaW5zLm1hcChwbHVnaW4gPT4gcGx1Z2luLm5hbWUgfHwgJyh1bm5hbWVkKScpLmpvaW4oJywgJyk7XG5cdFx0Y29uc29sZS5sb2coYExvYWRlZCB0YWN0aWNhIGNvbmZpZzogJHtjb25maWdQYXRofSAocGx1Z2luczogJHtuYW1lcyB8fCAnbm9uZSd9KWApO1xuXHR9XG5cblx0cmV0dXJuIHBsdWdpbnM7XG59XG5cbi8qKlxuICogUnVuIHR5cGUgZ2VuZXJhdGlvbi4gUmV0dXJucyAwIG9uIHN1Y2Nlc3M7IDEgd2hlbiB0aGUgZ3JhcGggaWRlbnRpdHkgbGF3XG4gKiBhYm9ydGVkIHRoZSBydW4gKGZhaWx1cmVzIHByaW50ZWQsIG5vIC50YWN0aWNhIG91dHB1dCB3cml0dGVuKS5cbiAqL1xuZnVuY3Rpb24gcnVuIChvcHRpb25zOiBDTElPcHRpb25zKTogbnVtYmVyIHtcblx0Y29uc3QgdHNjb25maWdQYXRoID0gZmluZFRzQ29uZmlnKG9wdGlvbnMucHJvamVjdCk7XG5cblx0aWYgKCF0c2NvbmZpZ1BhdGgpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjogQ291bGQgbm90IGZpbmQgdHNjb25maWcuanNvbicpO1xuXHRcdHByb2Nlc3MuZXhpdCgxKTtcblx0fVxuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgVXNpbmcgdHNjb25maWc6ICR7dHNjb25maWdQYXRofWApO1xuXHR9XG5cblx0Ly8gRnJhbWV3b3JrIHZvY2FidWxhcnkgYXJyaXZlcyB2aWEgcGx1Z2lucyDigJQgYSBjb25maWcgZmlsZSBuZXh0IHRvIHRoZVxuXHQvLyB0c2NvbmZpZyAob3IgaW4gY3dkKSBhbmQvb3IgcHJvZ3JhbW1hdGljIG9wdGlvbnMuIE5vbmUgbG9hZGVkIG1lYW5zXG5cdC8vIHRoZSBhbmFseXplciBkZXRlY3RzIHplcm8gaW5zdHJ1bWVudGF0aW9uIHBvaW50cy5cblx0Y29uc3QgcGx1Z2lucyA9IGxvYWRUYWN0aWNhUGx1Z2lucyhwYXRoLmRpcm5hbWUocGF0aC5yZXNvbHZlKHRzY29uZmlnUGF0aCkpLCBvcHRpb25zKTtcblxuXHQvLyBMb2FkIFR5cGVTY3JpcHQgcHJvZ3JhbVxuXHRjb25zdCBwcm9ncmFtID0gbG9hZFByb2dyYW0odHNjb25maWdQYXRoKTtcblxuXHQvLyBDcmVhdGUgYW5hbHl6ZXJcblx0Y29uc3QgYW5hbHl6ZXIgPSBuZXcgTW5lbW9uaWNhQW5hbHl6ZXIocHJvZ3JhbSwgcGx1Z2lucyk7XG5cblx0Ly8gRGV0ZXJtaW5lIG91dHB1dCBkaXJlY3RvcnkgZm9yIGV4Y2x1c2lvblxuXHRjb25zdCBvdXRwdXREaXIgPSBvcHRpb25zLm91dHB1dERpciB8fCAnLnRhY3RpY2EnO1xuXHRjb25zdCBvdXRwdXREaXJQYXRoID0gcGF0aC5yZXNvbHZlKHByb2Nlc3MuY3dkKCksIG91dHB1dERpcik7XG5cdC8vIFRoZSBwcm9qZWN0LWNvbnZlbnRpb25hbCAudGFjdGljYSBkaXIgKG5leHQgdG8gdHNjb25maWcpIGlzIEFMV0FZU1xuXHQvLyBleGNsdWRlZCwgZXZlbiB3aGVuIC0tb3V0cHV0IHBvaW50cyBlbHNld2hlcmU6IGdlbmVyYXRlZCBmaWxlcyBhcmVcblx0Ly8gbmV2ZXIgcHJvamVjdCBzb3VyY2UuIHJlc29sdmUoKSBib3RoIHNpZGVzIOKAlCB0c2NvbmZpZ1BhdGggbWF5IGJlXG5cdC8vIHJlbGF0aXZlICgnLi90c2NvbmZpZy5qc29uJykgd2hpbGUgc291cmNlRmlsZS5maWxlTmFtZSBpcyBhYnNvbHV0ZVxuXHRjb25zdCBjb252ZW50aW9uYWxPdXRwdXREaXIgPSBwYXRoLnJlc29sdmUocHJvY2Vzcy5jd2QoKSwgcGF0aC5kaXJuYW1lKHRzY29uZmlnUGF0aCksICcudGFjdGljYScpO1xuXHQvLyBhIGhhbmRsZXIgaW1wb3J0aW5nIGZyb20gZWl0aGVyIGRpciBuYW1lcyBpdHMgb3duIGdlbmVyYXRlZCB0eXBlXG5cdGFuYWx5emVyLnNldEdlbmVyYXRlZE91dHB1dERpcnMoWyBvdXRwdXREaXJQYXRoLCBjb252ZW50aW9uYWxPdXRwdXREaXIgXSk7XG5cblx0Ly8gQ29sbGVjdCBzb3VyY2UgZmlsZXMgdG8gYW5hbHl6ZVxuXHRjb25zdCBzb3VyY2VGaWxlczogdHMuU291cmNlRmlsZVtdID0gW107XG5cdGZvciAoY29uc3Qgc291cmNlRmlsZSBvZiBwcm9ncmFtLmdldFNvdXJjZUZpbGVzKCkpIHtcblx0XHRpZiAoc291cmNlRmlsZS5pc0RlY2xhcmF0aW9uRmlsZSkge1xuXHRcdFx0Y29udGludWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QgYWJzb2x1dGVGaWxlTmFtZSA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBzb3VyY2VGaWxlLmZpbGVOYW1lKTtcblx0XHRpZiAoYWJzb2x1dGVGaWxlTmFtZS5zdGFydHNXaXRoKG91dHB1dERpclBhdGggKyBwYXRoLnNlcCkgfHxcblx0XHRcdGFic29sdXRlRmlsZU5hbWUuc3RhcnRzV2l0aChjb252ZW50aW9uYWxPdXRwdXREaXIgKyBwYXRoLnNlcCkpIHtcblx0XHRcdGNvbnRpbnVlO1xuXHRcdH1cblxuXHRcdC8vIENoZWNrIGV4Y2x1ZGUgcGF0dGVybnNcblx0XHRpZiAob3B0aW9ucy5leGNsdWRlKSB7XG5cdFx0XHRjb25zdCBzaG91bGRFeGNsdWRlID0gb3B0aW9ucy5leGNsdWRlLnNvbWUocGF0dGVybiA9PlxuXHRcdFx0XHRzb3VyY2VGaWxlLmZpbGVOYW1lLmluY2x1ZGVzKHBhdHRlcm4ucmVwbGFjZSgvXFwqL2csICcnKSkpO1xuXHRcdFx0aWYgKHNob3VsZEV4Y2x1ZGUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Ly8gQ2hlY2sgaW5jbHVkZSBwYXR0ZXJuc1xuXHRcdGlmIChvcHRpb25zLmluY2x1ZGUgJiYgb3B0aW9ucy5pbmNsdWRlLmxlbmd0aCA+IDApIHtcblx0XHRcdGNvbnN0IHNob3VsZEluY2x1ZGUgPSBvcHRpb25zLmluY2x1ZGUuc29tZShwYXR0ZXJuID0+XG5cdFx0XHRcdHNvdXJjZUZpbGUuZmlsZU5hbWUuaW5jbHVkZXMocGF0dGVybi5yZXBsYWNlKC9cXCovZywgJycpKSk7XG5cdFx0XHRpZiAoIXNob3VsZEluY2x1ZGUpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0c291cmNlRmlsZXMucHVzaChzb3VyY2VGaWxlKTtcblx0fVxuXG5cdC8vIFNjYW4gZm9yIHRvcG9sb2dpY2EgZGlyZWN0b3J5IHN0cnVjdHVyZXMgRklSU1Rcblx0Y29uc3QgcHJvamVjdERpciA9IHBhdGguZGlybmFtZSh0c2NvbmZpZ1BhdGgpO1xuXHRjb25zdCB0b3BvbG9naWNhRGlycyA9IHNjYW5Ub3BvbG9naWNhRGlyZWN0b3JpZXMocHJvamVjdERpciwgb3B0aW9ucy50b3BvbG9naWNhRGlycyk7XG5cblx0aWYgKHRvcG9sb2dpY2FEaXJzLmxlbmd0aCA+IDAgJiYgb3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEZvdW5kIHRvcG9sb2dpY2EgZGlyZWN0b3JpZXM6ICR7dG9wb2xvZ2ljYURpcnMuam9pbignLCAnKX1gKTtcblx0fVxuXG5cdC8vIEFuYWx5emUgdG9wb2xvZ2ljYSBkaXJlY3RvcmllcyBCRUZPUkUgdXNhZ2UgY29sbGVjdGlvblxuXHRjb25zdCB0b3BvbG9naWNhQW5hbHl6ZXIgPSBuZXcgVG9wb2xvZ2ljYUFuYWx5emVyKCk7XG5cdGNvbnN0IHRvcG9sb2dpY2FUeXBlcyA9IG5ldyBNYXA8c3RyaW5nLCBpbXBvcnQoJy4vdHlwZXMnKS5UeXBlTm9kZT4oKTtcblx0Zm9yIChjb25zdCBkaXIgb2YgdG9wb2xvZ2ljYURpcnMpIHtcblx0XHRjb25zdCByZXN1bHQgPSB0b3BvbG9naWNhQW5hbHl6ZXIuYW5hbHl6ZURpcmVjdG9yeShkaXIpO1xuXHRcdGlmIChyZXN1bHQudHlwZXMuc2l6ZSA+IDApIHtcblx0XHRcdC8vIENvbGxlY3QgdG9wb2xvZ2ljYSB0eXBlcyBmb3IgZGVmaW5pdGlvbnMgYW5kIHVzYWdlIHRyYWNraW5nXG5cdFx0XHRmb3IgKGNvbnN0IFsgdHlwZVBhdGgsIG5vZGUgXSBvZiByZXN1bHQudHlwZXMpIHtcblx0XHRcdFx0dG9wb2xvZ2ljYVR5cGVzLnNldCh0eXBlUGF0aCwgbm9kZSk7XG5cdFx0XHR9XG5cdFx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRcdGNvbnNvbGUubG9nKGBBZGRlZCAke3Jlc3VsdC50eXBlcy5zaXplfSB0eXBlcyBmcm9tICR7ZGlyfWApO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRpZiAocmVzdWx0LmVycm9ycy5sZW5ndGggPiAwICYmIG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdFx0cmVzdWx0LmVycm9ycy5mb3JFYWNoKGVyciA9PiBjb25zb2xlLndhcm4oYFtUb3BvbG9naWNhXSAke2Vycn1gKSk7XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWRkIHRvcG9sb2dpY2EgdHlwZXMgdG8gYW5hbHl6ZXIgc28gdGhleSdyZSBhdmFpbGFibGUgZm9yIHVzYWdlIGRldGVjdGlvblxuXHQvLyBQcm9jZXNzIGluIG9yZGVyIG9mIHBhdGggZGVwdGggKHBhcmVudHMgZmlyc3QpIHRvIGVuc3VyZSBwcm9wZXIgaGllcmFyY2h5XG5cdGNvbnN0IHNvcnRlZFR5cGVzID0gQXJyYXkuZnJvbSh0b3BvbG9naWNhVHlwZXMuZW50cmllcygpKS5zb3J0KChhLCBiKSA9PiB7XG5cdFx0Y29uc3QgZGVwdGhBID0gKGFbIDAgXS5tYXRjaCgvXFwuL2cpIHx8IFtdKS5sZW5ndGg7XG5cdFx0Y29uc3QgZGVwdGhCID0gKGJbIDAgXS5tYXRjaCgvXFwuL2cpIHx8IFtdKS5sZW5ndGg7XG5cdFx0cmV0dXJuIGRlcHRoQSAtIGRlcHRoQjtcblx0fSk7XG5cdGZvciAoY29uc3QgWyB0eXBlUGF0aCwgbm9kZSBdIG9mIHNvcnRlZFR5cGVzKSB7XG5cdFx0YW5hbHl6ZXIuYWRkVG9wb2xvZ2ljYVR5cGUodHlwZVBhdGgsIG5vZGUpO1xuXHR9XG5cblx0Ly8gRmlyc3QgcGFzczogY29sbGVjdCBhbGwgZGVmaW5pdGlvbnMuXG5cdC8vIE1vZHVsZS1zY29wZSB0cmFja2luZyAoaW1wb3J0cy9leHBvcnRzIGZvciBtb2R1bGVzLmpzb24pIGhhcHBlbnMgaW4gdGhlXG5cdC8vIHNhbWUgcGFzcyDigJQgaXQgbmVlZHMgb25seSB0aGUgQVNULCBub3QgdGhlIGNvbGxlY3RlZCBkZWZpbml0aW9ucy5cblx0Y29uc3QgbW9kdWxlR3JhcGhCdWlsZGVyID0gbmV3IE1vZHVsZUdyYXBoQnVpbGRlcihwcm9ncmFtKTtcblx0Ly8gQW5hbHl6ZXIgZXJyb3JzIChlLmcuIGFuIHVubmFtZWQgbGF6eSgpIGNhbGwpIG5ldmVyIGFib3J0IHRoZSBydW4g4oCUXG5cdC8vIHRoZSBvZmZlbmRpbmcgY2FsbCBpcyBzaW1wbHkgc2tpcHBlZCDigJQgYnV0IHRoZXkgYXJlIEFMV0FZUyBwcmludGVkLFxuXHQvLyBvbmNlIGVhY2g6IGJvdGggcGFzc2VzIHZpc2l0IHRoZSBzYW1lIGNhbGwgc2l0ZXMsIHNvIGRlZHVwZSBieSBrZXkuXG5cdGNvbnN0IGFuYWx5emVyRXJyb3JzOiBBbmFseXplRXJyb3JbXSA9IFtdO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgQW5hbHl6aW5nIChkZWZpbml0aW9ucyk6ICR7c291cmNlRmlsZS5maWxlTmFtZX1gKTtcblx0XHR9XG5cblx0XHR0cnkge1xuXHRcdFx0Y29uc3QgZGVmaW5pdGlvbnNQYXNzID0gYW5hbHl6ZXIuYW5hbHl6ZUZpbGUoc291cmNlRmlsZSk7XG5cdFx0XHRhbmFseXplckVycm9ycy5wdXNoKC4uLmRlZmluaXRpb25zUGFzcy5lcnJvcnMpO1xuXHRcdFx0bW9kdWxlR3JhcGhCdWlsZGVyLmFkZEZpbGUoc291cmNlRmlsZSk7XG5cdFx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0XHRjb25zb2xlLmVycm9yKGBFcnJvciBhbmFseXppbmcgJHtzb3VyY2VGaWxlLmZpbGVOYW1lfTpgLCBlcnIpO1xuXHRcdFx0dGhyb3cgZXJyO1xuXHRcdH1cblx0fVxuXG5cdC8vIFNlY29uZCBwYXNzOiBjb2xsZWN0IHVzYWdlcyAobm93IGFsbCBkZWZpbml0aW9ucyBhcmUga25vd24sIGluY2x1ZGluZyB0b3BvbG9naWNhKVxuXHRhbmFseXplci5yZXNldFVzYWdlcygpO1xuXHRmb3IgKGNvbnN0IHNvdXJjZUZpbGUgb2Ygc291cmNlRmlsZXMpIHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgQW5hbHl6aW5nICh1c2FnZXMpOiAke3NvdXJjZUZpbGUuZmlsZU5hbWV9YCk7XG5cdFx0fVxuXG5cdFx0dHJ5IHtcblx0XHRcdGNvbnN0IHVzYWdlc1Bhc3MgPSBhbmFseXplci5hbmFseXplRmlsZShzb3VyY2VGaWxlKTtcblx0XHRcdGFuYWx5emVyRXJyb3JzLnB1c2goLi4udXNhZ2VzUGFzcy5lcnJvcnMpO1xuXHRcdH0gY2F0Y2ggKGVycikge1xuXHRcdFx0Y29uc29sZS5lcnJvcihgRXJyb3IgYW5hbHl6aW5nICR7c291cmNlRmlsZS5maWxlTmFtZX06YCwgZXJyKTtcblx0XHRcdHRocm93IGVycjtcblx0XHR9XG5cdH1cblxuXHRjb25zdCBzZWVuV2FybmluZ3MgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0Zm9yIChjb25zdCBhbmFseXplckVycm9yIG9mIGFuYWx5emVyRXJyb3JzKSB7XG5cdFx0Y29uc3Qga2V5ID0gYCR7YW5hbHl6ZXJFcnJvci5maWxlfToke2FuYWx5emVyRXJyb3IubGluZX06JHthbmFseXplckVycm9yLmNvbHVtbn06JHthbmFseXplckVycm9yLm1lc3NhZ2V9YDtcblx0XHRpZiAoc2Vlbldhcm5pbmdzLmhhcyhrZXkpKSB7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cdFx0c2Vlbldhcm5pbmdzLmFkZChrZXkpO1xuXHRcdGNvbnN0IHJlbEZpbGUgPSBwYXRoLnJlbGF0aXZlKHByb2plY3REaXIsIGFuYWx5emVyRXJyb3IuZmlsZSk7XG5cdFx0Y29uc29sZS53YXJuKGB0YWN0aWNhOiAke3JlbEZpbGV9OiR7YW5hbHl6ZXJFcnJvci5saW5lfToke2FuYWx5emVyRXJyb3IuY29sdW1ufSAke2FuYWx5emVyRXJyb3IubWVzc2FnZX1gKTtcblx0fVxuXG5cdC8vIEdlbmVyYXRlIHR5cGVzIGZyb20gbW5lbW9uaWNhIGFuYWx5c2lzXG5cdC8vIE5vdGU6IHRvcG9sb2dpY2EgdHlwZXMgYXJlIGFscmVhZHkgYWRkZWQgdG8gdGhlIGFuYWx5emVyJ3MgZ3JhcGggdmlhIGFkZFRvcG9sb2dpY2FUeXBlKClcblx0Y29uc3QgZ3JhcGggPSBhbmFseXplci5nZXRHcmFwaCgpO1xuXG5cdC8vIFBhdGgtYXdhcmUgZ3JhcGggcmVmZXJlbmNlIHJlc29sdXRpb24gKGlkZW50aXR5IGxhdyk6IHRoZSBnZW5lcmF0b3Jcblx0Ly8gcmVzb2x2ZXMgbmFtZXMgdGhyb3VnaCB0aGUgc2FtZSByZWxhdGl2ZS1maXJzdC9yb290L3VuaXF1ZSB0aWVycyB0aGVcblx0Ly8gYW5hbHl6ZXIgdXNlczsgdGhlIGFuYWx5emVyJ3Mgb3duIHZhbHVlL2ltcG9ydCB0aWVycyBhbHJlYWR5IHZldHRlZCB0aGVcblx0Ly8gdHlwZSBzdHJpbmdzIGR1cmluZyBleHRyYWN0aW9uXG5cdGNvbnN0IHJlZmVyZW5jZVJlc29sdmVyOiBHcmFwaFJlZmVyZW5jZVJlc29sdmVyID0gKHNpbXBsZU5hbWUsIGFuY2hvcikgPT4ge1xuXHRcdGNvbnN0IHJlZlJlc3VsdCA9IHJlc29sdmVHcmFwaFR5cGVSZWZlcmVuY2UoZ3JhcGgsIHNpbXBsZU5hbWUsIGFuY2hvcik7XG5cdFx0aWYgKHJlZlJlc3VsdC5zdGF0dXMgPT09ICd1bmlxdWUnKSB7XG5cdFx0XHRyZXR1cm4gcmVmUmVzdWx0Lm5vZGU7XG5cdFx0fVxuXHRcdGlmIChyZWZSZXN1bHQuc3RhdHVzID09PSAnYW1iaWd1b3VzJykge1xuXHRcdFx0cmV0dXJuICdhbWJpZ3VvdXMnO1xuXHRcdH1cblx0XHRyZXR1cm4gdW5kZWZpbmVkO1xuXHR9O1xuXHRjb25zdCBnZW5lcmF0b3IgPSBuZXcgVHlwZXNHZW5lcmF0b3IoXG5cdFx0Z3JhcGgsXG5cdFx0b3B0aW9ucy5lc20sXG5cdFx0b3B0aW9ucy5vdXRwdXREaXIsXG5cdFx0cmVmZXJlbmNlUmVzb2x2ZXIsXG5cdFx0YW5hbHl6ZXIuZ2V0QnVpbGRlclZhbHVlcygpXG5cdCk7XG5cblx0Ly8gR2VuZXJhdGUgZXZlcnl0aGluZyBpbnRvIG1lbW9yeSBGSVJTVCDigJQgdGhlIGhhcmQtZmFpbCBsYXcgYmVsb3cgbWF5XG5cdC8vIGFib3J0IHRoZSBydW4sIGFuZCBubyAudGFjdGljYSBvdXRwdXQgYXQgYWxsIG1heSBiZSB3cml0dGVuIHRoZW5cblx0Y29uc3QgZ2VuZXJhdGVkVHlwZXMgPSBnZW5lcmF0b3IuZ2VuZXJhdGVUeXBlc0ZpbGUoKTtcblx0Y29uc3QgcmVnaXN0cnlUeXBlcyA9IGdlbmVyYXRvci5nZW5lcmF0ZVR5cGVSZWdpc3RyeSgpO1xuXG5cdC8vIEhBUkQgRkFJTCAoZ3JhcGggaWRlbnRpdHkgbGF3KTogc2FtZS1uYW1lc3BhY2UgZHVwbGljYXRlIG1uZW1vbmljYVxuXHQvLyBkZWZpbml0aW9ucywgcGx1cyBncmFwaCByZWZlcmVuY2VzIHRoYXQgc3RheSBhbWJpZ3VvdXMgYWZ0ZXJcblx0Ly8gcGF0aC1hd2FyZSByZXNvbHV0aW9uIG9yIHJlc29sdmUgdG8gbm90aGluZy4gUHJpbnQgZXZlcnkgZmFpbHVyZSB3aXRoXG5cdC8vIGFsbCBpdHMgbG9jYXRpb25zIGFuZCB3cml0ZSBOTyAudGFjdGljYSBvdXRwdXQgYXQgYWxsLlxuXHRjb25zdCBmYXRhbEVycm9ycyA9IFsgLi4uYW5hbHl6ZXIuZ2V0UmVzb2x1dGlvbkVycm9ycygpLCAuLi5nZW5lcmF0b3IuZ2V0UmVzb2x1dGlvbkVycm9ycygpIF07XG5cdGlmIChmYXRhbEVycm9ycy5sZW5ndGggPiAwKSB7XG5cdFx0Y29uc3Qgc2VlbiA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdGxldCBwcmludGVkID0gMDtcblx0XHRmb3IgKGNvbnN0IGVycm9yIG9mIGZhdGFsRXJyb3JzKSB7XG5cdFx0XHRjb25zdCBrZXkgPSBgJHtlcnJvci5tZXNzYWdlfXwke2Vycm9yLmxvY2F0aW9ucy5qb2luKCd8Jyl9YDtcblx0XHRcdGlmIChzZWVuLmhhcyhrZXkpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0c2Vlbi5hZGQoa2V5KTtcblx0XHRcdHByaW50ZWQrKztcblx0XHRcdGNvbnNvbGUuZXJyb3IoYHRhY3RpY2E6ICR7ZXJyb3IubWVzc2FnZX1gKTtcblx0XHRcdGZvciAoY29uc3QgbG9jYXRpb24gb2YgZXJyb3IubG9jYXRpb25zKSB7XG5cdFx0XHRcdGNvbnNvbGUuZXJyb3IoYCAgYXQgJHtsb2NhdGlvbn1gKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0Y29uc29sZS5lcnJvcihgdGFjdGljYTogYWJvcnRpbmcg4oCUICR7cHJpbnRlZH0gcmVzb2x1dGlvbiBmYWlsdXJlKHMpOyBubyAudGFjdGljYSBvdXRwdXQgd3JpdHRlbmApO1xuXHRcdHJldHVybiAxO1xuXHR9XG5cblx0Ly8gUHJvamVjdCByb290IGFuY2hvcnMgdGhlIHJlbGF0aXZlIHBhdGhzIHRoZSB3cml0ZXIgZW1pdHM6IC50YWN0aWNhXG5cdC8vIG91dHB1dCBtdXN0IHN0YXkgcG9ydGFibGUgd2hlbiB0aGUgY2hlY2tvdXQgbW92ZXMgYmV0d2VlbiBtYWNoaW5lcy5cblx0Ly8gcmVzb2x2ZSgpIGJvdGggc2lkZXMg4oCUIHRzY29uZmlnUGF0aCBpdHNlbGYgbWF5IGJlIHJlbGF0aXZlLlxuXHRjb25zdCBwcm9qZWN0Um9vdCA9IHBhdGgucmVzb2x2ZShwcm9jZXNzLmN3ZCgpLCBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKSk7XG5cdGNvbnN0IHdyaXRlciA9IG5ldyBUeXBlc1dyaXRlcihvcHRpb25zLm91dHB1dERpciwgcHJvamVjdFJvb3QpO1xuXHQvLyBPbmUgcnVuOiB0aGUgZmlsZXMgYmVsb3cgYXJlIHdyaXR0ZW4gdG9nZXRoZXIgYXQgY29tbWl0KCksIG9yIG5vdFxuXHQvLyBhdCBhbGwgd2hlbiBvbmx5IHRoZWlyIGdlbmVyYXRlZEF0IHN0YW1wcyB3b3VsZCBjaGFuZ2Vcblx0d3JpdGVyLmJlZ2luKCk7XG5cblx0Y29uc3Qgb3V0cHV0UGF0aCA9IHdyaXRlci53cml0ZVR5cGVzRmlsZShnZW5lcmF0ZWRUeXBlcyk7XG5cdGNvbnN0IHJlZ2lzdHJ5UGF0aCA9IHdyaXRlci53cml0ZVRvKCdyZWdpc3RyeS50cycsIHJlZ2lzdHJ5VHlwZXMuY29udGVudCk7XG5cblx0Ly8gR2VuZXJhdGUgaW5kZXgudHMgdG8gZXhwb3J0IGV2ZXJ5dGhpbmdcblx0Y29uc3QgaW5kZXhDb250ZW50ID0gYC8vIEdlbmVyYXRlZCBieSBAbW5lbW9uaWNhL3RhY3RpY2EgLSBETyBOT1QgRURJVFxuLy8gRXhwb3J0IGFsbCBnZW5lcmF0ZWQgdHlwZXNcblxuZXhwb3J0ICogZnJvbSAnLi90eXBlcyR7b3B0aW9ucy5lc20gPyAnLmpzJyA6ICcnfSc7XG5leHBvcnQgKiBmcm9tICcuL3JlZ2lzdHJ5JHtvcHRpb25zLmVzbSA/ICcuanMnIDogJyd9JztcbmA7XG5cdHdyaXRlci53cml0ZVRvKCdpbmRleC50cycsIGluZGV4Q29udGVudCk7XG5cblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgcmVnaXN0cnkudHMgYXQ6ICR7cmVnaXN0cnlQYXRofWApO1xuXHR9XG5cblx0Ly8gR2VuZXJhdGUgZGVmaW5pdGlvbnMuanNvbiBhbmQgdXNhZ2VzLmpzb24gZm9yIGNvZGUgbmF2aWdhdGlvblxuXHQvLyBJbmNsdWRlIGJvdGggbW5lbW9uaWNhIGFuZCB0b3BvbG9naWNhIGRlZmluaXRpb25zXG5cdGNvbnN0IGRlZmluaXRpb25zID0gbmV3IE1hcChhbmFseXplci5nZXREZWZpbml0aW9ucygpKTtcblx0Y29uc3QgdXNhZ2VzID0gbmV3IE1hcChhbmFseXplci5nZXRVc2FnZXMoKSk7XG5cdFxuXHQvLyBBZGQgdG9wb2xvZ2ljYSB0eXBlcyB0byBkZWZpbml0aW9uc1xuXHRmb3IgKGNvbnN0IFsgZnVsbFBhdGgsIHR5cGVOb2RlIF0gb2YgdG9wb2xvZ2ljYVR5cGVzKSB7XG5cdFx0Ly8gU2tpcCBpZiBhbHJlYWR5IGV4aXN0cyAocHJlZmVyIG1uZW1vbmljYSdzIGFuYWx5c2lzKVxuXHRcdGlmIChkZWZpbml0aW9ucy5oYXMoZnVsbFBhdGgpKSB7XG5cdFx0XHRjb250aW51ZTtcblx0XHR9XG5cdFx0XG5cdFx0Y29uc3QgZGVmaW5pdGlvbjogaW1wb3J0KCcuL3R5cGVzJykuRGVmaW5pdGlvbkluZm8gPSB7XG5cdFx0XHRuYW1lICAgICAgICA6IHR5cGVOb2RlLm5hbWUsXG5cdFx0XHRsb2NhdGlvbiAgICA6IGAke3R5cGVOb2RlLnNvdXJjZUZpbGV9OiR7dHlwZU5vZGUubGluZX06JHt0eXBlTm9kZS5jb2x1bW59YCxcblx0XHRcdGtpbmQgICAgICAgIDogJ2RlZmluZScsXG5cdFx0XHRwYXJlbnQgICAgICA6IHR5cGVOb2RlLnBhcmVudCA/IHR5cGVOb2RlLnBhcmVudC5mdWxsUGF0aCA6IG51bGwsXG5cdFx0XHRzdHJpY3RDaGFpbiA6IHRydWUsXG5cdFx0XHRibG9ja0Vycm9ycyA6IGZhbHNlXG5cdFx0fTtcblx0XHRkZWZpbml0aW9ucy5zZXQoZnVsbFBhdGgsIGRlZmluaXRpb24pO1xuXHR9XG5cblx0Ly8gTG9jYWwtc2NvcGUgd2FsayAoaW5zdHJ1bWVudGF0aW9uIHdhbGtlciBQaGFzZSAyKTogZnVuY3Rpb24vbWV0aG9kL2Fycm93XG5cdC8vIHNjb3BlcyBvbmx5IChubyBibG9jayBzY29wZXMg4oCUIGRlY2lzaW9uIDUpLCB2YXJpYWJsZXMgd2l0aCBpc011dGFibGUgYW5kXG5cdC8vIHJlYXNzaWdubWVudCBzaXRlcyAoZGVjaXNpb24gNikuIFJ1bnMgYWZ0ZXIgZGVmaW5pdGlvbnMgYXJlIGtub3duIHNvXG5cdC8vIHZhcmlhYmxlIHR5cGVQYXRocyBjYW4gcmVzb2x2ZTsgaG9sZGVyU2NvcGVJZCBpcyBhdHRhY2hlZCB0byB1c2FnZXNcblx0Ly8gYmVmb3JlIHRoZXkgYXJlIHdyaXR0ZW4uXG5cdGNvbnN0IHNjb3BlV2Fsa2VyID0gbmV3IExvY2FsU2NvcGVXYWxrZXIoKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0c2NvcGVXYWxrZXIuYWRkRmlsZShzb3VyY2VGaWxlKTtcblx0fVxuXHRjb25zdCBzY29wZVJlc29sdmVyOiBTY29wZVR5cGVSZXNvbHZlciA9IHtcblx0XHRyZXNvbHZlQnlOYW1lIDogKG5hbWU6IHN0cmluZyk6IHN0cmluZyB8IHVuZGVmaW5lZCA9PiB7XG5cdFx0XHRpZiAoZGVmaW5pdGlvbnMuaGFzKG5hbWUpKSB7XG5cdFx0XHRcdHJldHVybiBuYW1lO1xuXHRcdFx0fVxuXHRcdFx0bGV0IGZvdW5kOiBzdHJpbmcgfCB1bmRlZmluZWQ7XG5cdFx0XHRmb3IgKGNvbnN0IFsgZnVsbFBhdGgsIGRlZmluaXRpb24gXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdFx0XHRpZiAoZGVmaW5pdGlvbi5uYW1lICE9PSBuYW1lKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKGZvdW5kKSB7XG5cdFx0XHRcdFx0Ly8gQW1iaWd1b3VzIG5hbWUg4oCUIG5vIHR5cGUgY2hlY2tlciwgc28gcmVmdXNlIHRvIGd1ZXNzXG5cdFx0XHRcdFx0cmV0dXJuIHVuZGVmaW5lZDtcblx0XHRcdFx0fVxuXHRcdFx0XHRmb3VuZCA9IGZ1bGxQYXRoO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGZvdW5kO1xuXHRcdH0sXG5cdFx0aGFzUGF0aCA6IChmdWxsUGF0aDogc3RyaW5nKTogYm9vbGVhbiA9PiB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBkZWZpbml0aW9ucy5oYXMoZnVsbFBhdGgpO1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9LFxuXHRcdC8vIFRoZSBhbmFseXplcidzIG93biBsb29rdXAgbGF3LCBhZ2FpbnN0IHRoZSBzYW1lIGNvbXBsZXRlIGdyYXBoIHRoZVxuXHRcdC8vIHVzYWdlcyBwYXNzIHJlc29sdmVkIHdpdGgg4oCUIGEgbG9va3VwKCkgaW5pdGlhbGl6ZXIgdGhlIGFuYWx5emVyXG5cdFx0Ly8gYWNjZXB0ZWQgKGUuZy4gYW4gaW1wb3J0ZWQgSG9sZGVyLmxvb2t1cCgnVG9rZW4nKSkgbGFuZHMgdGhlIHNhbWVcblx0XHQvLyBmdWxsUGF0aCBpbiBzY29wZXMuanNvbiBpbnN0ZWFkIG9mIHN0YXJ2aW5nIHRoZSBjcmVhdGlvbi1ncmFwaFxuXHRcdC8vIGFuY2hvcnMuIFJlamVjdGVkIGxvb2t1cHMgc3RheSB0eXBlUGF0aC1sZXNzIGhlcmU7IHRoZSBhbmFseXplclxuXHRcdC8vIGFscmVhZHkgaGFyZC1mYWlsZWQgdGhlIHJ1biBhYm92ZS5cblx0XHRyZXNvbHZlTG9va3VwIDogKGNhbGw6IHRzLkNhbGxFeHByZXNzaW9uKTogc3RyaW5nIHwgdW5kZWZpbmVkID0+IHtcblx0XHRcdGNvbnN0IHJlc29sdmVkID0gYW5hbHl6ZXIucmVzb2x2ZUxvb2t1cENhbGxQYXRoKGNhbGwpO1xuXHRcdFx0cmV0dXJuIHJlc29sdmVkO1xuXHRcdH0sXG5cdH07XG5cdGNvbnN0IHNjb3BlQW5hbHlzaXMgPSBzY29wZVdhbGtlci5idWlsZChzY29wZVJlc29sdmVyKTtcblx0TG9jYWxTY29wZVdhbGtlci5hdHRhY2hIb2xkZXJTY29wZUlkcyh1c2FnZXMsIHNjb3BlV2Fsa2VyKTtcblxuXHRjb25zdCBkZWZpbml0aW9uc1BhdGggPSB3cml0ZXIud3JpdGVEZWZpbml0aW9uc0ZpbGUoZGVmaW5pdGlvbnMsIGdyYXBoKTtcblx0Y29uc3QgdXNhZ2VzUGF0aCA9IHdyaXRlci53cml0ZVVzYWdlc0ZpbGUodXNhZ2VzKTtcblxuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBkZWZpbml0aW9ucy5qc29uIGF0OiAke2RlZmluaXRpb25zUGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHVzYWdlcy5qc29uIGF0OiAke3VzYWdlc1BhdGh9YCk7XG5cdH1cblxuXHQvLyBEZXRlcm1pbmUgRURTIHNldHRpbmc6IGV4cGxpY2l0IGZsYWcgPiBhdXRvLWRldGVjdCBkaXZlID4gZGVmYXVsdCBvZmZcblx0bGV0IGVuYWJsZUVEUyA9IG9wdGlvbnMuZWRzO1xuXHRpZiAoZW5hYmxlRURTID09PSB1bmRlZmluZWQpIHtcblx0XHRlbmFibGVFRFMgPSBoYXNEaXZlRGVwZW5kZW5jeShwcm9qZWN0RGlyKTtcblx0fVxuXG5cdGlmIChlbmFibGVFRFMpIHtcblx0XHRjb25zdCBlZHMgPSBhbmFseXplci5nZXRFRFNVc2FnZXMoKTtcblx0XHRhdHRhY2hXcmFwSm9pbkRhdGEoZWRzLCBzY29wZVdhbGtlciwgc2NvcGVBbmFseXNpcyk7XG5cdFx0Y29uc3QgZWRzUGF0aCA9IHdyaXRlci53cml0ZUVEU0ZpbGUoZWRzKTtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGVkcy5qc29uIGF0OiAke2Vkc1BhdGh9YCk7XG5cdFx0fVxuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIGZsb3cuanNvbiAobmF0aXZlIGluc3RhbmNlIHVzYWdlIHRyYWNraW5nKVxuXHRjb25zdCBmbG93ID0gYW5hbHl6ZXIuZ2V0Rmxvd1VzYWdlcygpO1xuXHRjb25zdCBmbG93UGF0aCA9IHdyaXRlci53cml0ZUZsb3dGaWxlKGZsb3cpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3QgZmxvd0NvdW50ID0gQXJyYXkuZnJvbShmbG93LnZhbHVlcygpKS5yZWR1Y2UoKHN1bSwgYXJyKSA9PiBzdW0gKyBhcnIubGVuZ3RoLCAwKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGZsb3cuanNvbiBhdDogJHtmbG93UGF0aH0gKCR7Zmxvd0NvdW50fSBmbG93IGVudHJpZXMpYCk7XG5cdH1cblxuXHQvLyBBbHdheXMgZ2VuZXJhdGUgbW9kdWxlcy5qc29uIChtb2R1bGUtc2NvcGUgZ3JhcGg6IGltcG9ydHMvZXhwb3J0cyxcblx0Ly8gZGVwZW5kZW5jaWVzLCBjeWNsZXMsIGNyb3NzLW1vZHVsZSBtbmVtb25pY2EtdHlwZSBlZGdlcylcblx0Y29uc3QgZGVmaW5lZFR5cGVzQnlGaWxlID0gbmV3IE1hcDxzdHJpbmcsIHN0cmluZ1tdPigpO1xuXHRmb3IgKGNvbnN0IFsgZnVsbFBhdGgsIGRlZmluaXRpb24gXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdGNvbnN0IHsgbG9jYXRpb24gfSA9IGRlZmluaXRpb247XG5cdFx0Y29uc3QgbGFzdENvbG9uID0gbG9jYXRpb24ubGFzdEluZGV4T2YoJzonKTtcblx0XHRjb25zdCBwcmV2Q29sb24gPSBsb2NhdGlvbi5sYXN0SW5kZXhPZignOicsIGxhc3RDb2xvbiAtIDEpO1xuXHRcdGNvbnN0IGZpbGUgPSBsb2NhdGlvbi5zbGljZSgwLCBwcmV2Q29sb24pO1xuXHRcdGNvbnN0IGxpc3QgPSBkZWZpbmVkVHlwZXNCeUZpbGUuZ2V0KGZpbGUpID8/IFtdO1xuXHRcdGxpc3QucHVzaChmdWxsUGF0aCk7XG5cdFx0ZGVmaW5lZFR5cGVzQnlGaWxlLnNldChmaWxlLCBsaXN0KTtcblx0fVxuXHRjb25zdCBtb2R1bGVHcmFwaCA9IG1vZHVsZUdyYXBoQnVpbGRlci5idWlsZChkZWZpbmVkVHlwZXNCeUZpbGUpO1xuXHRjb25zdCBtb2R1bGVzUGF0aCA9IHdyaXRlci53cml0ZU1vZHVsZXNGaWxlKG1vZHVsZUdyYXBoKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IG1vZHVsZUNvdW50ID0gbW9kdWxlR3JhcGgubW9kdWxlcy5zaXplO1xuXHRcdGNvbnN0IGVkZ2VDb3VudCA9IG1vZHVsZUdyYXBoLmVkZ2VzLmxlbmd0aDtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIG1vZHVsZXMuanNvbiBhdDogJHttb2R1bGVzUGF0aH0gKCR7bW9kdWxlQ291bnR9IG1vZHVsZXMsICR7ZWRnZUNvdW50fSBlZGdlcylgKTtcblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBzY29wZXMuanNvbiAobG9jYWwtc2NvcGUgd2Fsa2VyOiBzY29wZXMsIHZhcmlhYmxlcyxcblx0Ly8gcmVhc3NpZ25tZW50IGZsb3ctdGVybWluYXRpb24gcG9pbnRzKVxuXHRjb25zdCBzY29wZXNQYXRoID0gd3JpdGVyLndyaXRlU2NvcGVzRmlsZShzY29wZUFuYWx5c2lzKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnN0IHNjb3BlQ291bnQgPSBzY29wZUFuYWx5c2lzLnNjb3Blcy5zaXplO1xuXHRcdGNvbnN0IHZhcmlhYmxlQ291bnQgPSBzY29wZUFuYWx5c2lzLnZhcmlhYmxlcy5zaXplO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgc2NvcGVzLmpzb24gYXQ6ICR7c2NvcGVzUGF0aH0gKCR7c2NvcGVDb3VudH0gc2NvcGVzLCAke3ZhcmlhYmxlQ291bnR9IHZhcmlhYmxlcylgKTtcblx0fVxuXG5cdC8vIFRoZSBpbnNpZGUtb3V0IGNyZWF0aW9uIHdhbGsgKGluc3RydW1lbnRhdGlvbiB3YWxrZXIgUGhhc2UgMyk6IGFuY2hvcnNcblx0Ly8gYXJlIHRoZSBpbnN0YW50aWF0aW9uIHVzYWdlczsgY2FsbGVycyBhcmUgZm9sbG93ZWQgc2FtZS1maWxlIGFuZFxuXHQvLyBjcm9zcy1maWxlIChtb2R1bGUgZ3JhcGgsIGJhcnJlbHMgY2hhc2VkKSB1bnRpbCBvbmx5IHN0YXJ0ZXJzIHJlbWFpbi5cblx0Y29uc3Qgc291cmNlRmlsZXNCeVBhdGggPSBuZXcgTWFwPHN0cmluZywgdHMuU291cmNlRmlsZT4oKTtcblx0Zm9yIChjb25zdCBzb3VyY2VGaWxlIG9mIHNvdXJjZUZpbGVzKSB7XG5cdFx0c291cmNlRmlsZXNCeVBhdGguc2V0KHBhdGgucmVzb2x2ZShzb3VyY2VGaWxlLmZpbGVOYW1lKSwgc291cmNlRmlsZSk7XG5cdH1cblx0Y29uc3QgY3JlYXRpb25HcmFwaEJ1aWxkZXIgPSBuZXcgQ3JlYXRpb25HcmFwaEJ1aWxkZXIobW9kdWxlR3JhcGgsIHNjb3BlQW5hbHlzaXMsIHNjb3BlV2Fsa2VyLCBzb3VyY2VGaWxlc0J5UGF0aCk7XG5cdGNvbnN0IGNyZWF0aW9uR3JhcGggPSBjcmVhdGlvbkdyYXBoQnVpbGRlci5idWlsZCh1c2FnZXMpO1xuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBpbnN0cnVtZW50YXRpb24uanNvbiAoZnJhbWV3b3JrIGxpZmVjeWNsZSBjcm9zc3JvYWRzXG5cdC8vIGZyb20gdGhlIGxvYWRlZCBwbHVnaW5zIOKAlCBzeW50YWN0aWMgZGV0ZWN0aW9uIG5lZWRzIG5vIGRpdmVcblx0Ly8gZGVwZW5kZW5jeSwgdW5saWtlIGVkcy5qc29uKS4gdjIgY2FycmllcyB0aGUgY3JlYXRpb24gZ3JhcGhcblx0Ly8gYWxvbmdzaWRlIHRoZSBwb2ludHMuXG5cdGNvbnN0IGluc3RydW1lbnRhdGlvbiA9IGFuYWx5emVyLmdldEluc3RydW1lbnRhdGlvblBvaW50cygpO1xuXHRjb25zdCBpbnN0cnVtZW50YXRpb25QYXRoID0gd3JpdGVyLndyaXRlSW5zdHJ1bWVudGF0aW9uRmlsZShpbnN0cnVtZW50YXRpb24sIGNyZWF0aW9uR3JhcGgpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc3Qgbm9kZUNvdW50ID0gY3JlYXRpb25HcmFwaC5ub2Rlcy5sZW5ndGg7XG5cdFx0Y29uc3QgZWRnZUNvdW50ID0gY3JlYXRpb25HcmFwaC5lZGdlcy5sZW5ndGg7XG5cdFx0Y29uc3QgYW5jaG9yQ291bnQgPSBjcmVhdGlvbkdyYXBoLmFuY2hvcnMubGVuZ3RoO1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgaW5zdHJ1bWVudGF0aW9uLmpzb24gYXQ6ICR7aW5zdHJ1bWVudGF0aW9uUGF0aH0gKCR7aW5zdHJ1bWVudGF0aW9uLmxlbmd0aH0gcG9pbnRzKWApO1xuXHRcdGNvbnNvbGUubG9nKGAgIGNyZWF0aW9uIGdyYXBoOiAke25vZGVDb3VudH0gbm9kZXMsICR7ZWRnZUNvdW50fSBlZGdlcywgJHthbmNob3JDb3VudH0gYW5jaG9yc2ApO1xuXHR9XG5cblx0Ly8gQWx3YXlzIGdlbmVyYXRlIGNvbnRyb2wuanNvbiAobGV0aGUgY29udHJhY3QsIGZvcm1hdCAxLjIpOiB0aGUgc2FtZVxuXHQvLyBjcmVhdGlvbiBncmFwaCBhbmQgcG9pbnRzIGFzIGluc3RydW1lbnRhdGlvbi5qc29uLCByZW5kZXJlZCB1bmRlciB0aGVcblx0Ly8gY3Jvc3MtbGFuZ3VhZ2UgYGNhbGxlcnNgL2Bwb2ludHNgIGtleXMuXG5cdGNvbnN0IGNvbnRyb2xQYXRoID0gd3JpdGVyLndyaXRlQ29udHJvbEZpbGUoaW5zdHJ1bWVudGF0aW9uLCBjcmVhdGlvbkdyYXBoKTtcblx0aWYgKG9wdGlvbnMudmVyYm9zZSkge1xuXHRcdGNvbnNvbGUubG9nKGBHZW5lcmF0ZWQgY29udHJvbC5qc29uIGF0OiAke2NvbnRyb2xQYXRofWApO1xuXHR9XG5cblx0Ly8gR2VuZXJhdGUgaGllcmFyY2h5Lmpzb24gKHN0cnVjdHVyZWQpIGFuZCBoaWVyYXJjaHkudHh0IChBU0NJSSB0cmVlKSBmb3IgdGhlIFRyaWVcblx0Y29uc3QgaGllcmFyY2h5Um9vdHMgPSBncmFwaC50b0hpZXJhcmNoeSgpO1xuXHRjb25zdCBoaWVyYXJjaHlKc29uUGF0aCA9IHdyaXRlci53cml0ZUhpZXJhcmNoeUZpbGUoaGllcmFyY2h5Um9vdHMpO1xuXHRjb25zdCBoaWVyYXJjaHlUZXh0ID0gcmVuZGVyVHlwZUhpZXJhcmNoeShncmFwaCk7XG5cdGNvbnN0IGhpZXJhcmNoeVR4dFBhdGggPSB3cml0ZXIud3JpdGVUbygnaGllcmFyY2h5LnR4dCcsIGhpZXJhcmNoeVRleHQpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBoaWVyYXJjaHkuanNvbiBhdDogJHtoaWVyYXJjaHlKc29uUGF0aH1gKTtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIGhpZXJhcmNoeS50eHQgYXQ6ICR7aGllcmFyY2h5VHh0UGF0aH1gKTtcblx0fVxuXG5cdC8vIEFsd2F5cyBnZW5lcmF0ZSBjb2xsZWN0aW9ucy5qc29uICh0aGUgY29sbGVjdGlvbiBtYW5pZmVzdDogaWRzLCBkaXNwbGF5XG5cdC8vIG5hbWVzLCBPcHRpb24tQiByZWdpc3RyeSBpbnRlcmZhY2VzLCBjYWxsIHNpdGVzIOKAlCB0aGUgaWTihpRpbnRlcmZhY2Ugam9pblxuXHQvLyBrZXkgYmV0d2VlbiB0aGUgcHJlZml4ZWQgZ3JhcGggb3V0cHV0cyBhbmQgdGhlIHR5cGVzLnRzIGFsaWFzZXMpXG5cdGNvbnN0IGNvbGxlY3Rpb25zUGF0aCA9IHdyaXRlci53cml0ZUNvbGxlY3Rpb25zRmlsZShhbmFseXplci5nZXRDb2xsZWN0aW9uc01hbmlmZXN0KCkpO1xuXHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCBjb2xsZWN0aW9ucy5qc29uIGF0OiAke2NvbGxlY3Rpb25zUGF0aH1gKTtcblx0fVxuXG5cdGNvbnN0IHdyaXR0ZW4gPSB3cml0ZXIuY29tbWl0KCk7XG5cdGNvbnN0IHVuY2hhbmdlZE5vdGUgPSB3cml0dGVuID8gJycgOiAnICh1bmNoYW5nZWQsIG5vdGhpbmcgd3JpdHRlbiknO1xuXG5cdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRjb25zb2xlLmxvZyhgR2VuZXJhdGVkIHR5cGVzIGF0OiAke291dHB1dFBhdGh9JHt1bmNoYW5nZWROb3RlfWApO1xuXHRcdGNvbnNvbGUubG9nKCdNb2RlOiB0eXBlcyBmaWxlIChkZWZhdWx0KScpO1xuXHRcdGNvbnNvbGUubG9nKGBGb3VuZCAke2dlbmVyYXRlZFR5cGVzLnR5cGVzLmxlbmd0aH0gdHlwZXM6YCk7XG5cdFx0cHJpbnRUeXBlSGllcmFyY2h5KGdyYXBoKTtcblx0fSBlbHNlIHtcblx0XHRjb25zdCBzaG93bkRpciA9IG9wdGlvbnMub3V0cHV0RGlyIHx8ICcudGFjdGljYSc7XG5cdFx0Y29uc29sZS5sb2coYEdlbmVyYXRlZCAke2dlbmVyYXRlZFR5cGVzLnR5cGVzLmxlbmd0aH0gdHlwZXMgYXQgJHtzaG93bkRpcn0ke3VuY2hhbmdlZE5vdGV9YCk7XG5cdH1cblxuXHRyZXR1cm4gMDtcbn1cblxuLyoqXG4gKiBXYXRjaCBtb2RlXG4gKi9cbmZ1bmN0aW9uIHdhdGNoIChvcHRpb25zOiBDTElPcHRpb25zKTogdm9pZCB7XG5cdGNvbnNvbGUubG9nKCdTdGFydGluZyB3YXRjaCBtb2RlLi4uJyk7XG5cblx0Ly8gSW5pdGlhbCBydW5cblx0cnVuKG9wdGlvbnMpO1xuXG5cdC8vIFNldCB1cCBmaWxlIHdhdGNoaW5nXG5cdGNvbnN0IGNob2tpZGFyID0gcmVxdWlyZSgnY2hva2lkYXInKTtcblx0Y29uc3QgdHNjb25maWdQYXRoID0gZmluZFRzQ29uZmlnKG9wdGlvbnMucHJvamVjdCk7XG5cblx0aWYgKCF0c2NvbmZpZ1BhdGgpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjogQ291bGQgbm90IGZpbmQgdHNjb25maWcuanNvbicpO1xuXHRcdHByb2Nlc3MuZXhpdCgxKTtcblx0fVxuXG5cdGNvbnN0IHByb2plY3REaXIgPSBwYXRoLmRpcm5hbWUodHNjb25maWdQYXRoKTtcblx0Y29uc3Qgd2F0Y2hQYXRocyA9IG9wdGlvbnMuaW5jbHVkZSB8fCBbICcqKi8qLnRzJyBdO1xuXHRjb25zdCBpZ25vcmVQYXRocyA9IG9wdGlvbnMuZXhjbHVkZSB8fCBbICcqKi8qLmQudHMnLCAnbm9kZV9tb2R1bGVzLyoqJywgJy50YWN0aWNhLyoqJyBdO1xuXG5cdGNvbnN0IHdhdGNoZXIgPSBjaG9raWRhci53YXRjaCh3YXRjaFBhdGhzLCB7XG5cdFx0Y3dkICAgICAgICA6IHByb2plY3REaXIsXG5cdFx0aWdub3JlZCAgICA6IGlnbm9yZVBhdGhzLFxuXHRcdHBlcnNpc3RlbnQgOiB0cnVlLFxuXHR9KTtcblxuXHR3YXRjaGVyLm9uKCdjaGFuZ2UnLCAoZmlsZVBhdGg6IHN0cmluZykgPT4ge1xuXHRcdGlmIChvcHRpb25zLnZlcmJvc2UpIHtcblx0XHRcdGNvbnNvbGUubG9nKGBGaWxlIGNoYW5nZWQ6ICR7ZmlsZVBhdGh9YCk7XG5cdFx0fVxuXHRcdHJ1bihvcHRpb25zKTtcblx0fSk7XG5cblx0d2F0Y2hlci5vbignYWRkJywgKGZpbGVQYXRoOiBzdHJpbmcpID0+IHtcblx0XHRpZiAob3B0aW9ucy52ZXJib3NlKSB7XG5cdFx0XHRjb25zb2xlLmxvZyhgRmlsZSBhZGRlZDogJHtmaWxlUGF0aH1gKTtcblx0XHR9XG5cdFx0cnVuKG9wdGlvbnMpO1xuXHR9KTtcblxuXHRjb25zb2xlLmxvZygnV2F0Y2hpbmcgZm9yIGNoYW5nZXMuLi4gKFByZXNzIEN0cmwrQyB0byBzdG9wKScpO1xufVxuXG4vKipcbiAqIE1haW4gZW50cnkgcG9pbnRcbiAqL1xuZnVuY3Rpb24gbWFpbiAoKTogdm9pZCB7XG5cdGNvbnN0IGFyZ3MgPSBwcm9jZXNzLmFyZ3Yuc2xpY2UoMik7XG5cdGNvbnN0IG9wdGlvbnMgPSBwYXJzZUFyZ3MoYXJncyk7XG5cblx0aWYgKG9wdGlvbnMuaGVscCkge1xuXHRcdHByaW50SGVscCgpO1xuXHRcdHByb2Nlc3MuZXhpdCgwKTtcblx0fVxuXG5cdHRyeSB7XG5cdFx0aWYgKG9wdGlvbnMud2F0Y2gpIHtcblx0XHRcdHdhdGNoKG9wdGlvbnMpO1xuXHRcdH0gZWxzZSB7XG5cdFx0XHRjb25zdCBjb2RlID0gcnVuKG9wdGlvbnMpO1xuXHRcdFx0aWYgKGNvZGUpIHtcblx0XHRcdFx0cHJvY2Vzcy5leGl0KGNvZGUpO1xuXHRcdFx0fVxuXHRcdH1cblx0fSBjYXRjaCAoZXJyb3IpIHtcblx0XHRjb25zb2xlLmVycm9yKCdFcnJvcjonLCBlcnJvciBpbnN0YW5jZW9mIEVycm9yID8gZXJyb3IubWVzc2FnZSA6IGVycm9yKTtcblx0XHRwcm9jZXNzLmV4aXQoMSk7XG5cdH1cbn1cblxuLy8gUnVuIGlmIGV4ZWN1dGVkIGRpcmVjdGx5XG5pZiAocmVxdWlyZS5tYWluID09PSBtb2R1bGUpIHtcblx0bWFpbigpO1xufVxuXG5leHBvcnQge1xuXHRtYWluLCBydW4sIHdhdGNoLCBwYXJzZUFyZ3MgXG59O1xuIl19