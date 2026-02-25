'use strict';
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.VERSION = exports.default = exports.parseArgs = exports.watch = exports.run = exports.main = exports.create = exports.decorate = exports.define = exports.TypesWriter = exports.TypesGenerator = exports.TypeGraphImpl = exports.MnemonicaAnalyzer = void 0;
/**
 * Tactica - TypeScript Language Service Plugin for Mnemonica
 *
 * Generates type definitions for Mnemonica's dynamic nested constructors,
 * enabling TypeScript to understand runtime type hierarchies created through
 * define() and decorate() calls.
 */
var analyzer_1 = require("./analyzer");
Object.defineProperty(exports, "MnemonicaAnalyzer", { enumerable: true, get: function () { return analyzer_1.MnemonicaAnalyzer; } });
var graph_1 = require("./graph");
Object.defineProperty(exports, "TypeGraphImpl", { enumerable: true, get: function () { return graph_1.TypeGraphImpl; } });
var generator_1 = require("./generator");
Object.defineProperty(exports, "TypesGenerator", { enumerable: true, get: function () { return generator_1.TypesGenerator; } });
var writer_1 = require("./writer");
Object.defineProperty(exports, "TypesWriter", { enumerable: true, get: function () { return writer_1.TypesWriter; } });
// Tactica's enhanced define function
var define_1 = require("./define");
Object.defineProperty(exports, "define", { enumerable: true, get: function () { return define_1.define; } });
Object.defineProperty(exports, "decorate", { enumerable: true, get: function () { return define_1.decorate; } });
Object.defineProperty(exports, "create", { enumerable: true, get: function () { return define_1.create; } });
// CLI entry point
var cli_1 = require("./cli");
Object.defineProperty(exports, "main", { enumerable: true, get: function () { return cli_1.main; } });
Object.defineProperty(exports, "run", { enumerable: true, get: function () { return cli_1.run; } });
Object.defineProperty(exports, "watch", { enumerable: true, get: function () { return cli_1.watch; } });
Object.defineProperty(exports, "parseArgs", { enumerable: true, get: function () { return cli_1.parseArgs; } });
// Plugin entry point (for TypeScript Language Service)
var plugin_1 = require("./plugin");
Object.defineProperty(exports, "default", { enumerable: true, get: function () { return __importDefault(plugin_1).default; } });
// Version
exports.VERSION = '0.1.0';
//# sourceMappingURL=index.js.map