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
let definitionsMap = new Map();
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
        // Override getDefinitionAtPosition to provide Go to Definition for lookupTyped
        proxy.getDefinitionAtPosition = (fileName, position) => {
            // Debug logging - this should appear in TypeScript logs when Ctrl+Click happens
            info.project.projectService.logger.info(`[TACTICA PLUGIN ACTIVE] getDefinitionAtPosition called: ${fileName}:${position}`);
            console.log(`[TACTICA PLUGIN] getDefinitionAtPosition called: ${fileName}:${position}`);
            // TEMPORARY: Just log and return undefined to test if plugin is working
            // Remove this once we confirm the plugin is being called
            info.project.projectService.logger.info('[TACTICA PLUGIN] Test mode - returning undefined to verify plugin is active');
            return undefined;
            // TODO: Re-enable this once plugin is confirmed working
            // First check if this is a lookupTyped string literal
            // const lookupDefinition = getLookupTypedDefinition(fileName, position, info, tsModule);
            // if (lookupDefinition) {
            // 	info.project.projectService.logger.info(`[Tactica] Returning lookup definition: ${lookupDefinition.length} results`);
            // 	return lookupDefinition;
            // }
            // return oldService.getDefinitionAtPosition(fileName, position);
        };
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
 * Check if the position is inside a lookupTyped('TypeName') call's string literal
 * and return definition info for that type
 * TEMPORARILY COMMENTED OUT FOR PLUGIN TESTING
 */
/*
function getLookupTypedDefinition(
    fileName: string,
    position: number,
    info: ts.server.PluginCreateInfo,
    tsModule: typeof ts
): readonly ts.DefinitionInfo[] | undefined {
    info.project.projectService.logger.info(`[Tactica] getLookupTypedDefinition called`);

    const program = info.languageService.getProgram();
    if (!program) {
        info.project.projectService.logger.info(`[Tactica] No program found`);
        return undefined;
    }

    const sourceFile = program.getSourceFile(fileName);
    if (!sourceFile) {
        info.project.projectService.logger.info(`[Tactica] No source file found for ${fileName}`);
        return undefined;
    }

    // Find the token at the current position
    const token = findTokenAtPosition(sourceFile, position, tsModule);
    if (!token) {
        info.project.projectService.logger.info(`[Tactica] No token found at position ${position}`);
        return undefined;
    }

    info.project.projectService.logger.info(`[Tactica] Token kind: ${tsModule.SyntaxKind[token.kind]}`);

    // Check if the token is a string literal
    if (!tsModule.isStringLiteral(token) && !tsModule.isNoSubstitutionTemplateLiteral(token)) {
        info.project.projectService.logger.info(`[Tactica] Token is not a string literal`);
        return undefined;
    }

    info.project.projectService.logger.info(`[Tactica] Token text: ${token.text}`);

    // Check if this string is the first argument to lookupTyped()
    const typePath = token.text;
    const parent = token.parent;

    if (!tsModule.isCallExpression(parent)) {
        return undefined;
        }
    
        const funcName = getFunctionName(parent.expression, tsModule);
        info.project.projectService.logger.info(`[Tactica] Function name: ${funcName}`);
        if (funcName !== 'lookupTyped') {
            info.project.projectService.logger.info(`[Tactica] Not lookupTyped, returning`);
            return undefined;
        }
    
        // Check that this is the first argument
        if (parent.arguments[0] !== token) {
            info.project.projectService.logger.info(`[Tactica] Not first argument`);
            return undefined;
        }
    
        // Look up the type in definitions
        info.project.projectService.logger.info(`[Tactica] Looking up type: ${typePath}, definitionsMap size: ${definitionsMap.size}`);
        const definition = definitionsMap.get(typePath);
        if (!definition) {
            info.project.projectService.logger.info(`[Tactica] Definition not found for ${typePath}`);
            return undefined;
        }
    
        info.project.projectService.logger.info(`[Tactica] Found definition: ${definition.location}`);
    
        // Parse location (format: file.ts:line:column)
        const locationMatch = definition.location.match(/^(.+):(\d+):(\d+)$/);
        if (!locationMatch) {
            return undefined;
        }
    
        const [, defFilePath, lineStr, colStr] = locationMatch;
        const line = parseInt(lineStr, 10) - 1; // 0-based
        const col = parseInt(colStr, 10) - 1;   // 0-based
    
        // Get the source file for the definition
        const defSourceFile = program.getSourceFile(defFilePath);
        if (!defSourceFile) {
            return undefined;
        }
    
        // Calculate the position
        const defPosition = defSourceFile.getPositionOfLineAndCharacter(line, col);
    
        // Find the identifier or node at that position to use as text span
        const defToken = findTokenAtPosition(defSourceFile, defPosition, tsModule);
        if (!defToken) {
            return undefined;
        }
    
        // Create definition info
        const textSpan: ts.TextSpan = {
            start: defToken.getStart(defSourceFile),
            length: defToken.getWidth(defSourceFile),
        };
    
        return [{
            fileName: defFilePath,
            textSpan,
            kind: tsModule.ScriptElementKind.classElement,
            name: definition.name,
            containerName: definition.parent || '',
            containerKind: tsModule.ScriptElementKind.moduleElement,
        }];
    }
    */
/**
 * Find token at position using TypeScript's internal API
 * TEMPORARILY COMMENTED OUT FOR PLUGIN TESTING
 */
/*
function findTokenAtPosition(sourceFile: ts.SourceFile, position: number, tsModule: typeof ts): ts.Node | undefined {
    // Use the language service to get the node at position
    function find(node: ts.Node): ts.Node | undefined {
        if (position >= node.getStart(sourceFile) && position < node.getEnd()) {
            let result: ts.Node | undefined;
            tsModule.forEachChild(node, child => {
                if (!result) {
                    const found = find(child);
                    if (found) {
                        result = found;
                    }
                }
            });
            return result || node;
        }
        return undefined;
    }
    return find(sourceFile);
}
*/
/**
 * Get function name from expression (identifier or property access)
 * TEMPORARILY COMMENTED OUT FOR PLUGIN TESTING
 */
/*
function getFunctionName(expr: ts.Expression, tsModule: typeof ts): string | undefined {
    if (tsModule.isIdentifier(expr)) {
        return expr.text;
    }
    if (tsModule.isPropertyAccessExpression(expr)) {
        return expr.name.text;
    }
    return undefined;
}
*/
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
        // Scan for topologica directories
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
        // Update definitions map for Go to Definition
        definitionsMap = analyzer.getDefinitions();
        // Also add topologica types to definitions
        for (const [fullPath, typeNode] of typeGraph.allTypes) {
            if (!definitionsMap.has(fullPath)) {
                // For topologica types, ensure we point to the actual file (index.ts), not directory
                let location = `${typeNode.sourceFile}:${typeNode.line}:${typeNode.column}`;
                if (fs.existsSync(typeNode.sourceFile) && fs.statSync(typeNode.sourceFile).isDirectory()) {
                    // If sourceFile is a directory, look for index.ts
                    const indexPath = path.join(typeNode.sourceFile, 'index.ts');
                    if (fs.existsSync(indexPath)) {
                        location = `${indexPath}:1:1`;
                    }
                }
                const definition = {
                    name: typeNode.name,
                    location,
                    kind: 'define',
                    parent: typeNode.parent ? typeNode.parent.fullPath : null,
                    strictChain: true,
                    blockErrors: false,
                };
                definitionsMap.set(fullPath, definition);
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