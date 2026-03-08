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
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const analyzer_1 = require("./analyzer");
const topologica_analyzer_1 = require("./topologica-analyzer");
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
 * Merge topologica types into mnemonica graph
 */
function mergeTopologicaTypes(graph, topologicaTypes) {
    for (const [fullPath, typeNode] of topologicaTypes) {
        // Skip if already exists in graph (prefer mnemonica's TypeScript analysis)
        if (graph.allTypes.has(fullPath)) {
            continue;
        }
        // Add to graph - parent relationship is already set in typeNode
        if (typeNode.parent) {
            // Add as child of parent
            graph.addChild(typeNode.parent, typeNode);
        }
        else {
            // Add as root
            graph.addRoot(typeNode);
        }
    }
}
/**
 * Scan for topologica directory structures
 */
function scanTopologicaDirectories(projectDir) {
    const dirs = [];
    const possibleDirs = ['ai-types', 'types', 'topologica-types'];
    for (const dirName of possibleDirs) {
        const dirPath = path.join(projectDir, dirName);
        if (fs.existsSync(dirPath) && fs.statSync(dirPath).isDirectory()) {
            dirs.push(dirPath);
        }
    }
    // Also scan src/ subdirectory
    const srcPath = path.join(projectDir, 'src');
    if (fs.existsSync(srcPath) && fs.statSync(srcPath).isDirectory()) {
        for (const dirName of possibleDirs) {
            const dirPath = path.join(srcPath, dirName);
            if (fs.existsSync(dirPath) && fs.statSync(dirPath).isDirectory()) {
                dirs.push(dirPath);
            }
        }
    }
    return dirs;
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
        // Get the graph from mnemonica analysis
        typeGraph = analyzer.getGraph();
        // Scan for topologica directory structures
        const projectDir = info.project.getCurrentDirectory();
        const topologicaDirs = scanTopologicaDirectories(projectDir);
        // Analyze topologica directories and merge into graph
        const topologicaAnalyzer = new topologica_analyzer_1.TopologicaAnalyzer();
        for (const dir of topologicaDirs) {
            const result = topologicaAnalyzer.analyzeDirectory(dir);
            if (result.types.size > 0) {
                mergeTopologicaTypes(typeGraph, result.types);
                if (config.verbose) {
                    info.project.projectService.logger.info(`[Tactica] Added ${result.types.size} types from topologica directory: ${dir}`);
                }
            }
        }
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