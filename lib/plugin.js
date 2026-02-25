'use strict';
const analyzer_1 = require("./analyzer");
const graph_1 = require("./graph");
const generator_1 = require("./generator");
const writer_1 = require("./writer");
let pluginInfo;
let typeGraph = new graph_1.TypeGraphImpl();
/**
 * Initialize the plugin
 */
function init(modules) {
    const tsModule = modules.typescript;
    function create(info) {
        const config = info.config || {};
        config.outputDir = config.outputDir || '.tactica';
        // Store plugin info
        pluginInfo = {
            config,
            project: info.project,
            serverHost: info.serverHost,
            moduleResolver: info.project,
        };
        // Set up file watching
        setupFileWatcher(info, tsModule);
        // Initial type generation
        generateTypes(info, tsModule);
        // Wrap the language service to intercept requests if needed
        const proxy = Object.create(null);
        const oldService = info.languageService;
        for (const key of Object.keys(oldService)) {
            const fn = oldService[key];
            proxy[key] = (...args) => {
                return fn.apply(oldService, args);
            };
        }
        return proxy;
    }
    function onConfigurationChanged(config) {
        if (pluginInfo) {
            pluginInfo.config = { ...pluginInfo.config, ...config };
        }
    }
    return {
        create,
        onConfigurationChanged,
    };
}
/**
 * Set up file watching for incremental updates
 */
function setupFileWatcher(info, _tsModule) {
    const serverHost = info.serverHost;
    // Hook into file change notifications
    const originalFileChanged = serverHost.fileChanged;
    if (originalFileChanged) {
        serverHost.fileChanged = function (...args) {
            const result = originalFileChanged.apply(this, args);
            // Regenerate types when files change
            generateTypes(info, _tsModule);
            return result;
        };
    }
}
/**
 * Generate types from the project
 */
function generateTypes(info, _tsModule) {
    try {
        const program = info.languageService.getProgram();
        if (!program) {
            return;
        }
        const config = pluginInfo?.config || { outputDir: '.tactica' };
        const include = config.include || ['**/*.ts'];
        const exclude = config.exclude || ['**/*.d.ts', 'node_modules/**'];
        // Create analyzer
        const analyzer = new analyzer_1.MnemonicaAnalyzer(program);
        // Clear existing graph
        typeGraph.clear();
        // Analyze all source files
        for (const sourceFile of program.getSourceFiles()) {
            // Skip declaration files and files outside the project
            if (sourceFile.isDeclarationFile) {
                continue;
            }
            const fileName = sourceFile.fileName;
            // Check exclude patterns
            if (exclude.some(pattern => matchesGlob(fileName, pattern))) {
                continue;
            }
            // Check include patterns (if specified)
            if (include.length > 0 && !include.some(pattern => matchesGlob(fileName, pattern))) {
                continue;
            }
            // Analyze the file
            analyzer.analyzeFile(sourceFile);
        }
        // Get the graph and generate types
        typeGraph = analyzer.getGraph();
        const generator = new generator_1.TypesGenerator(typeGraph);
        const generated = generator.generateTypesFile();
        // Write types to file
        const writer = new writer_1.TypesWriter(config.outputDir);
        const outputPath = writer.writeTypesFile(generated);
        // Log success
        if (config.verbose) {
            info.project.projectService.logger.info(`[Tactica] Generated types at ${outputPath} (${generated.types.length} types)`);
        }
    }
    catch (error) {
        info.project.projectService.logger.info(`[Tactica] Error generating types: ${error}`);
    }
}
/**
 * Simple glob matching function
 */
function matchesGlob(filePath, pattern) {
    // Convert glob pattern to regex
    const regexPattern = pattern
        .replace(/\*\*/g, '<<<DOUBLESTAR>>>')
        .replace(/\*/g, '[^/]*')
        .replace(/<<<DOUBLESTAR>>>/g, '.*')
        .replace(/\?/g, '.');
    const regex = new RegExp(regexPattern);
    return regex.test(filePath);
}
module.exports = init;
//# sourceMappingURL=plugin.js.map