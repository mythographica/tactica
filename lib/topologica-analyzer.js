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
exports.TopologicaAnalyzer = void 0;
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const graph_1 = require("./graph");
/**
 * Analyzer for Topologica directory-based type definitions
 * Scans directory structures to create type hierarchies like:
 * ai-types/Sentience/Consciousness/Empathy/Gratitude/
 */
class TopologicaAnalyzer {
    constructor() {
        this.errors = [];
        this.graph = new graph_1.TypeGraphImpl();
    }
    /**
     * Analyze a directory structure for topologica type definitions
     */
    analyzeDirectory(directoryPath) {
        this.errors = [];
        if (!fs.existsSync(directoryPath)) {
            this.errors.push(`Directory does not exist: ${directoryPath}`);
            return { types: this.graph.allTypes, errors: this.errors };
        }
        if (!fs.statSync(directoryPath).isDirectory()) {
            this.errors.push(`Path is not a directory: ${directoryPath}`);
            return { types: this.graph.allTypes, errors: this.errors };
        }
        this.scanDirectory(directoryPath, undefined, directoryPath);
        return {
            types: this.graph.allTypes,
            errors: this.errors,
        };
    }
    /**
     * Recursively scan directory structure to build type hierarchy
     */
    scanDirectory(currentPath, parentNode, rootPath) {
        try {
            const entries = fs.readdirSync(currentPath, { withFileTypes: true });
            for (const entry of entries) {
                if (entry.isDirectory()) {
                    // Create type node for this directory
                    const typeName = entry.name;
                    const fullPath = parentNode ? `${parentNode.fullPath}.${typeName}` : typeName;
                    // Create the type node
                    const typeNode = {
                        name: typeName,
                        fullPath: fullPath,
                        properties: new Map(),
                        parent: parentNode,
                        children: new Map(),
                        sourceFile: currentPath,
                        line: 0,
                        column: 0,
                        constructorName: typeName
                    };
                    // Add to graph
                    if (parentNode) {
                        this.graph.addChild(parentNode, typeNode);
                    }
                    else {
                        // Add as root type
                        this.graph.addRoot(typeNode);
                    }
                    // Scan children of this directory
                    this.scanDirectory(path.join(currentPath, entry.name), typeNode, rootPath);
                }
            }
        }
        catch (error) {
            this.errors.push(`Error scanning directory ${currentPath}: ${error.message}`);
        }
    }
    /**
     * Get the type graph
     */
    getGraph() {
        return this.graph;
    }
    /**
     * Get collected errors
     */
    getErrors() {
        return this.errors;
    }
}
exports.TopologicaAnalyzer = TopologicaAnalyzer;
//# sourceMappingURL=topologica-analyzer.js.map