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
exports.VERSION = exports.parseArgs = exports.watch = exports.run = exports.main = exports.TypesWriter = exports.TypesGenerator = exports.TypeGraphImpl = exports.TopologicaAnalyzer = exports.MnemonicaAnalyzer = void 0;
const pkg = __importStar(require("../package.json"));
/**
 * Tactica - TypeScript Language Service Plugin for Mnemonica
 *
 * Generates type definitions for Mnemonica's dynamic nested constructors,
 * enabling TypeScript to understand runtime type hierarchies created through
 * define() and decorate() calls.
 */
var analyzer_1 = require("./analyzer");
Object.defineProperty(exports, "MnemonicaAnalyzer", { enumerable: true, get: function () { return analyzer_1.MnemonicaAnalyzer; } });
var topologica_analyzer_1 = require("./topologica-analyzer");
Object.defineProperty(exports, "TopologicaAnalyzer", { enumerable: true, get: function () { return topologica_analyzer_1.TopologicaAnalyzer; } });
var graph_1 = require("./graph");
Object.defineProperty(exports, "TypeGraphImpl", { enumerable: true, get: function () { return graph_1.TypeGraphImpl; } });
var generator_1 = require("./generator");
Object.defineProperty(exports, "TypesGenerator", { enumerable: true, get: function () { return generator_1.TypesGenerator; } });
var writer_1 = require("./writer");
Object.defineProperty(exports, "TypesWriter", { enumerable: true, get: function () { return writer_1.TypesWriter; } });
// CLI entry point
var cli_1 = require("./cli");
Object.defineProperty(exports, "main", { enumerable: true, get: function () { return cli_1.main; } });
Object.defineProperty(exports, "run", { enumerable: true, get: function () { return cli_1.run; } });
Object.defineProperty(exports, "watch", { enumerable: true, get: function () { return cli_1.watch; } });
Object.defineProperty(exports, "parseArgs", { enumerable: true, get: function () { return cli_1.parseArgs; } });
// Version from package.json
exports.VERSION = pkg.version;
//# sourceMappingURL=index.js.map