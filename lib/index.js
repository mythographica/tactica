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
exports.VERSION = exports.parseArgs = exports.watch = exports.run = exports.main = exports.mergeTacticaPlugins = exports.CreationGraphBuilder = exports.LocalScopeWalker = exports.ModuleGraphBuilder = exports.TypesWriter = exports.TypesGenerator = exports.TypeGraphImpl = exports.TopologicaAnalyzer = exports.MnemonicaAnalyzer = void 0;
const pkg = __importStar(require("../package.json"));
/**
 * Tactica - Type definition generator for Mnemonica
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
var plugins_1 = require("./plugins");
Object.defineProperty(exports, "mergeTacticaPlugins", { enumerable: true, get: function () { return plugins_1.mergeTacticaPlugins; } });
// CLI entry point
var cli_1 = require("./cli");
Object.defineProperty(exports, "main", { enumerable: true, get: function () { return cli_1.main; } });
Object.defineProperty(exports, "run", { enumerable: true, get: function () { return cli_1.run; } });
Object.defineProperty(exports, "watch", { enumerable: true, get: function () { return cli_1.watch; } });
Object.defineProperty(exports, "parseArgs", { enumerable: true, get: function () { return cli_1.parseArgs; } });
// Version from package.json
exports.VERSION = pkg.version;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiaW5kZXguanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvaW5kZXgudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFFYixxREFBdUM7QUFFdkM7Ozs7OztHQU1HO0FBRUgsdUNBQStDO0FBQXRDLDZHQUFBLGlCQUFpQixPQUFBO0FBQzFCLDZEQUEyRDtBQUFsRCx5SEFBQSxrQkFBa0IsT0FBQTtBQUMzQixpQ0FBd0M7QUFBL0Isc0dBQUEsYUFBYSxPQUFBO0FBQ3RCLHlDQUE2QztBQUFwQywyR0FBQSxjQUFjLE9BQUE7QUFDdkIsbUNBQXVDO0FBQTlCLHFHQUFBLFdBQVcsT0FBQTtBQUNwQiwrQ0FBb0Q7QUFBM0Msa0hBQUEsa0JBQWtCLE9BQUE7QUFDM0IsbUNBQTRDO0FBQW5DLDBHQUFBLGdCQUFnQixPQUFBO0FBRXpCLG1EQUF3RDtBQUEvQyxzSEFBQSxvQkFBb0IsT0FBQTtBQUM3QixxQ0FBZ0Q7QUFBdkMsOEdBQUEsbUJBQW1CLE9BQUE7QUF3QzVCLGtCQUFrQjtBQUNsQiw2QkFFZTtBQURkLDJGQUFBLElBQUksT0FBQTtBQUFFLDBGQUFBLEdBQUcsT0FBQTtBQUFFLDRGQUFBLEtBQUssT0FBQTtBQUFFLGdHQUFBLFNBQVMsT0FBQTtBQUc1Qiw0QkFBNEI7QUFDZixRQUFBLE9BQU8sR0FBRyxHQUFHLENBQUMsT0FBTyxDQUFDIiwic291cmNlc0NvbnRlbnQiOlsiJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBwa2cgZnJvbSAnLi4vcGFja2FnZS5qc29uJztcblxuLyoqXG4gKiBUYWN0aWNhIC0gVHlwZSBkZWZpbml0aW9uIGdlbmVyYXRvciBmb3IgTW5lbW9uaWNhXG4gKlxuICogR2VuZXJhdGVzIHR5cGUgZGVmaW5pdGlvbnMgZm9yIE1uZW1vbmljYSdzIGR5bmFtaWMgbmVzdGVkIGNvbnN0cnVjdG9ycyxcbiAqIGVuYWJsaW5nIFR5cGVTY3JpcHQgdG8gdW5kZXJzdGFuZCBydW50aW1lIHR5cGUgaGllcmFyY2hpZXMgY3JlYXRlZCB0aHJvdWdoXG4gKiBkZWZpbmUoKSBhbmQgZGVjb3JhdGUoKSBjYWxscy5cbiAqL1xuXG5leHBvcnQgeyBNbmVtb25pY2FBbmFseXplciB9IGZyb20gJy4vYW5hbHl6ZXInO1xuZXhwb3J0IHsgVG9wb2xvZ2ljYUFuYWx5emVyIH0gZnJvbSAnLi90b3BvbG9naWNhLWFuYWx5emVyJztcbmV4cG9ydCB7IFR5cGVHcmFwaEltcGwgfSBmcm9tICcuL2dyYXBoJztcbmV4cG9ydCB7IFR5cGVzR2VuZXJhdG9yIH0gZnJvbSAnLi9nZW5lcmF0b3InO1xuZXhwb3J0IHsgVHlwZXNXcml0ZXIgfSBmcm9tICcuL3dyaXRlcic7XG5leHBvcnQgeyBNb2R1bGVHcmFwaEJ1aWxkZXIgfSBmcm9tICcuL21vZHVsZS1ncmFwaCc7XG5leHBvcnQgeyBMb2NhbFNjb3BlV2Fsa2VyIH0gZnJvbSAnLi9zY29wZXMnO1xuZXhwb3J0IHR5cGUgeyBTY29wZVR5cGVSZXNvbHZlciB9IGZyb20gJy4vc2NvcGVzJztcbmV4cG9ydCB7IENyZWF0aW9uR3JhcGhCdWlsZGVyIH0gZnJvbSAnLi9jcmVhdGlvbi1ncmFwaCc7XG5leHBvcnQgeyBtZXJnZVRhY3RpY2FQbHVnaW5zIH0gZnJvbSAnLi9wbHVnaW5zJztcbmV4cG9ydCB0eXBlIHtcblx0VGFjdGljYVBsdWdpbiwgSW5zdHJ1bWVudGF0aW9uVm9jYWJ1bGFyeVxufSBmcm9tICcuL3BsdWdpbnMnO1xuXG5cbmV4cG9ydCB0eXBlIHtcblx0VGFjdGljYUNvbmZpZyxcblx0VHlwZU5vZGUsXG5cdFR5cGVHcmFwaCxcblx0UHJvcGVydHlJbmZvLFxuXHRBbmFseXplUmVzdWx0LFxuXHRBbmFseXplRXJyb3IsXG5cdEdlbmVyYXRlZFR5cGVzLFxuXHREZWZpbml0aW9uSW5mbyxcblx0VXNhZ2VJbmZvLFxuXHREZWZpbml0aW9uc0pzb24sXG5cdFVzYWdlc0pzb24sXG5cdEluc3RydW1lbnRhdGlvbktpbmQsXG5cdEluc3RydW1lbnRhdGlvblNjb3BlLFxuXHRJbnN0cnVtZW50YXRpb25Qb2ludCxcblx0SW5zdHJ1bWVudGF0aW9uSnNvbixcblx0TW9kdWxlQmluZGluZ0tpbmQsXG5cdE1vZHVsZUltcG9ydEtpbmQsXG5cdE1vZHVsZUJpbmRpbmcsXG5cdE1vZHVsZUluZm8sXG5cdENyb3NzTW9kdWxlVXNhZ2UsXG5cdE1vZHVsZUdyYXBoLFxuXHRNb2R1bGVzSnNvbixcblx0U2NvcGVLaW5kLFxuXHRTY29wZUluZm8sXG5cdFNjb3BlVmFyaWFibGUsXG5cdFNjb3BlQW5hbHlzaXMsXG5cdFNjb3Blc0pzb24sXG5cdENyZWF0aW9uR3JhcGhOb2RlLFxuXHRDcmVhdGlvbkdyYXBoRWRnZSxcblx0Q3JlYXRpb25BbmNob3IsXG5cdENyZWF0aW9uR3JhcGgsXG59IGZyb20gJy4vdHlwZXMnO1xuXG4vLyBDTEkgZW50cnkgcG9pbnRcbmV4cG9ydCB7XG5cdG1haW4sIHJ1biwgd2F0Y2gsIHBhcnNlQXJncyBcbn0gZnJvbSAnLi9jbGknO1xuXG4vLyBWZXJzaW9uIGZyb20gcGFja2FnZS5qc29uXG5leHBvcnQgY29uc3QgVkVSU0lPTiA9IHBrZy52ZXJzaW9uO1xuIl19