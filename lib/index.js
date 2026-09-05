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
exports.VERSION = exports.parseArgs = exports.watch = exports.run = exports.main = exports.CreationGraphBuilder = exports.LocalScopeWalker = exports.ModuleGraphBuilder = exports.TypesWriter = exports.TypesGenerator = exports.TypeGraphImpl = exports.TopologicaAnalyzer = exports.MnemonicaAnalyzer = void 0;
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
var module_graph_1 = require("./module-graph");
Object.defineProperty(exports, "ModuleGraphBuilder", { enumerable: true, get: function () { return module_graph_1.ModuleGraphBuilder; } });
var scopes_1 = require("./scopes");
Object.defineProperty(exports, "LocalScopeWalker", { enumerable: true, get: function () { return scopes_1.LocalScopeWalker; } });
var creation_graph_1 = require("./creation-graph");
Object.defineProperty(exports, "CreationGraphBuilder", { enumerable: true, get: function () { return creation_graph_1.CreationGraphBuilder; } });
// CLI entry point
var cli_1 = require("./cli");
Object.defineProperty(exports, "main", { enumerable: true, get: function () { return cli_1.main; } });
Object.defineProperty(exports, "run", { enumerable: true, get: function () { return cli_1.run; } });
Object.defineProperty(exports, "watch", { enumerable: true, get: function () { return cli_1.watch; } });
Object.defineProperty(exports, "parseArgs", { enumerable: true, get: function () { return cli_1.parseArgs; } });
// Version from package.json
exports.VERSION = pkg.version;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiaW5kZXguanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvaW5kZXgudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYixxREFBdUM7QUFFdkM7Ozs7OztHQU1HO0FBRUgsdUNBQStDO0FBQXRDLDZHQUFBLGlCQUFpQixPQUFBO0FBQzFCLDZEQUEyRDtBQUFsRCx5SEFBQSxrQkFBa0IsT0FBQTtBQUMzQixpQ0FBd0M7QUFBL0Isc0dBQUEsYUFBYSxPQUFBO0FBQ3RCLHlDQUE2QztBQUFwQywyR0FBQSxjQUFjLE9BQUE7QUFDdkIsbUNBQXVDO0FBQTlCLHFHQUFBLFdBQVcsT0FBQTtBQUNwQiwrQ0FBb0Q7QUFBM0Msa0hBQUEsa0JBQWtCLE9BQUE7QUFDM0IsbUNBQTRDO0FBQW5DLDBHQUFBLGdCQUFnQixPQUFBO0FBRXpCLG1EQUF3RDtBQUEvQyxzSEFBQSxvQkFBb0IsT0FBQTtBQXFDN0Isa0JBQWtCO0FBQ2xCLDZCQUVlO0FBRGQsMkZBQUEsSUFBSSxPQUFBO0FBQUUsMEZBQUEsR0FBRyxPQUFBO0FBQUUsNEZBQUEsS0FBSyxPQUFBO0FBQUUsZ0dBQUEsU0FBUyxPQUFBO0FBRzVCLDRCQUE0QjtBQUNmLFFBQUEsT0FBTyxHQUFHLEdBQUcsQ0FBQyxPQUFPLENBQUMiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIHBrZyBmcm9tICcuLi9wYWNrYWdlLmpzb24nO1xuXG4vKipcbiAqIFRhY3RpY2EgLSBUeXBlU2NyaXB0IExhbmd1YWdlIFNlcnZpY2UgUGx1Z2luIGZvciBNbmVtb25pY2FcbiAqXG4gKiBHZW5lcmF0ZXMgdHlwZSBkZWZpbml0aW9ucyBmb3IgTW5lbW9uaWNhJ3MgZHluYW1pYyBuZXN0ZWQgY29uc3RydWN0b3JzLFxuICogZW5hYmxpbmcgVHlwZVNjcmlwdCB0byB1bmRlcnN0YW5kIHJ1bnRpbWUgdHlwZSBoaWVyYXJjaGllcyBjcmVhdGVkIHRocm91Z2hcbiAqIGRlZmluZSgpIGFuZCBkZWNvcmF0ZSgpIGNhbGxzLlxuICovXG5cbmV4cG9ydCB7IE1uZW1vbmljYUFuYWx5emVyIH0gZnJvbSAnLi9hbmFseXplcic7XG5leHBvcnQgeyBUb3BvbG9naWNhQW5hbHl6ZXIgfSBmcm9tICcuL3RvcG9sb2dpY2EtYW5hbHl6ZXInO1xuZXhwb3J0IHsgVHlwZUdyYXBoSW1wbCB9IGZyb20gJy4vZ3JhcGgnO1xuZXhwb3J0IHsgVHlwZXNHZW5lcmF0b3IgfSBmcm9tICcuL2dlbmVyYXRvcic7XG5leHBvcnQgeyBUeXBlc1dyaXRlciB9IGZyb20gJy4vd3JpdGVyJztcbmV4cG9ydCB7IE1vZHVsZUdyYXBoQnVpbGRlciB9IGZyb20gJy4vbW9kdWxlLWdyYXBoJztcbmV4cG9ydCB7IExvY2FsU2NvcGVXYWxrZXIgfSBmcm9tICcuL3Njb3Blcyc7XG5leHBvcnQgdHlwZSB7IFNjb3BlVHlwZVJlc29sdmVyIH0gZnJvbSAnLi9zY29wZXMnO1xuZXhwb3J0IHsgQ3JlYXRpb25HcmFwaEJ1aWxkZXIgfSBmcm9tICcuL2NyZWF0aW9uLWdyYXBoJztcblxuXG5leHBvcnQgdHlwZSB7XG5cdFRhY3RpY2FDb25maWcsXG5cdFR5cGVOb2RlLFxuXHRUeXBlR3JhcGgsXG5cdFByb3BlcnR5SW5mbyxcblx0QW5hbHl6ZVJlc3VsdCxcblx0QW5hbHl6ZUVycm9yLFxuXHRHZW5lcmF0ZWRUeXBlcyxcblx0RGVmaW5pdGlvbkluZm8sXG5cdFVzYWdlSW5mbyxcblx0RGVmaW5pdGlvbnNKc29uLFxuXHRVc2FnZXNKc29uLFxuXHRJbnN0cnVtZW50YXRpb25LaW5kLFxuXHRJbnN0cnVtZW50YXRpb25TY29wZSxcblx0SW5zdHJ1bWVudGF0aW9uUG9pbnQsXG5cdEluc3RydW1lbnRhdGlvbkpzb24sXG5cdE1vZHVsZUJpbmRpbmdLaW5kLFxuXHRNb2R1bGVJbXBvcnRLaW5kLFxuXHRNb2R1bGVCaW5kaW5nLFxuXHRNb2R1bGVJbmZvLFxuXHRDcm9zc01vZHVsZVVzYWdlLFxuXHRNb2R1bGVHcmFwaCxcblx0TW9kdWxlc0pzb24sXG5cdFNjb3BlS2luZCxcblx0U2NvcGVJbmZvLFxuXHRTY29wZVZhcmlhYmxlLFxuXHRTY29wZUFuYWx5c2lzLFxuXHRTY29wZXNKc29uLFxuXHRDcmVhdGlvbkdyYXBoTm9kZSxcblx0Q3JlYXRpb25HcmFwaEVkZ2UsXG5cdENyZWF0aW9uQW5jaG9yLFxuXHRDcmVhdGlvbkdyYXBoLFxufSBmcm9tICcuL3R5cGVzJztcblxuLy8gQ0xJIGVudHJ5IHBvaW50XG5leHBvcnQge1xuXHRtYWluLCBydW4sIHdhdGNoLCBwYXJzZUFyZ3MgXG59IGZyb20gJy4vY2xpJztcblxuLy8gVmVyc2lvbiBmcm9tIHBhY2thZ2UuanNvblxuZXhwb3J0IGNvbnN0IFZFUlNJT04gPSBwa2cudmVyc2lvbjtcbiJdfQ==