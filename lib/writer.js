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
exports.TypesWriter = void 0;
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
/**
 * Writes generated types to file system
 */
class TypesWriter {
    constructor(outputDir = '.tactica') {
        this.outputDir = outputDir;
    }
    /**
     * Legacy write method - delegates to writeTypesFile
     */
    write(generated) {
        return this.writeTypesFile(generated);
    }
    /**
     * Write types.ts file (exportable type aliases - default mode)
     */
    writeTypesFile(generated) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'types.ts');
        fs.writeFileSync(filePath, generated.content, 'utf-8');
        return filePath;
    }
    /**
     * Write global augmentation file (index.d.ts - module augmentation mode)
     */
    writeGlobalAugmentation(generated) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'index.d.ts');
        fs.writeFileSync(filePath, generated.content, 'utf-8');
        return filePath;
    }
    /**
     * Write to a custom filename
     */
    writeTo(filename, content) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, filename);
        fs.writeFileSync(filePath, content, 'utf-8');
        return filePath;
    }
    /**
     * Ensure output directory exists
     */
    ensureDirectory() {
        if (!fs.existsSync(this.outputDir)) {
            fs.mkdirSync(this.outputDir, { recursive: true });
        }
    }
    /**
     * Clean the output directory
     */
    clean() {
        if (fs.existsSync(this.outputDir)) {
            const files = fs.readdirSync(this.outputDir);
            for (const file of files) {
                fs.unlinkSync(path.join(this.outputDir, file));
            }
        }
    }
    /**
     * Get output directory
     */
    getOutputDir() {
        return this.outputDir;
    }
    /**
     * Write definitions.json file
     */
    writeDefinitionsFile(definitions) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'definitions.json');
        // Convert Map to plain object
        const definitionsObj = {};
        for (const [key, value] of definitions) {
            definitionsObj[key] = value;
        }
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            definitions: definitionsObj,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write usages.json file
     */
    writeUsagesFile(usages) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'usages.json');
        // Convert Map to plain object
        const usagesObj = {};
        for (const [key, value] of usages) {
            usagesObj[key] = value;
        }
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            usages: usagesObj,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write eds.json file
     */
    writeEDSFile(eds) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'eds.json');
        // Convert Map to plain object
        const edsObj = {};
        for (const [key, value] of eds) {
            edsObj[key] = value;
        }
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            eds: edsObj,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write instrumentation.json file (v2: adds the creationGraph key when
     * the caller passes creation-graph data — the CLI always does)
     */
    writeInstrumentationFile(points, creationGraph) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'instrumentation.json');
        const json = {
            version: 2,
            generatedAt: new Date().toISOString(),
            points,
        };
        if (creationGraph) {
            json.creationGraph = creationGraph;
        }
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write flow.json file
     */
    writeFlowFile(flow) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'flow.json');
        // Convert Map to plain object
        const flowObj = {};
        for (const [key, value] of flow) {
            flowObj[key] = value;
        }
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            flow: flowObj,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write modules.json file
     */
    writeModulesFile(graph) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'modules.json');
        // Convert Map to plain object
        const modulesObj = {};
        for (const [key, value] of graph.modules) {
            modulesObj[key] = value;
        }
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            modules: modulesObj,
            edges: graph.edges,
            cycles: graph.cycles,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write scopes.json file
     */
    writeScopesFile(analysis) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'scopes.json');
        // Convert Maps to plain shapes
        const scopesObj = {};
        for (const [key, value] of analysis.scopes) {
            scopesObj[key] = value;
        }
        const variables = Array.from(analysis.variables.values());
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            scopes: scopesObj,
            variables,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write hierarchy.json file
     */
    writeHierarchyFile(roots) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'hierarchy.json');
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            roots,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
}
exports.TypesWriter = TypesWriter;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoid3JpdGVyLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL3dyaXRlci50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLHVDQUF5QjtBQUN6QiwyQ0FBNkI7QUFNN0I7O0dBRUc7QUFDSCxNQUFhLFdBQVc7SUFHdkIsWUFBYSxTQUFTLEdBQUcsVUFBVTtRQUNsQyxJQUFJLENBQUMsU0FBUyxHQUFHLFNBQVMsQ0FBQztJQUM1QixDQUFDO0lBRUQ7O09BRUc7SUFDSCxLQUFLLENBQUUsU0FBeUI7UUFDL0IsT0FBTyxJQUFJLENBQUMsY0FBYyxDQUFDLFNBQVMsQ0FBQyxDQUFDO0lBQ3ZDLENBQUM7SUFFRDs7T0FFRztJQUNILGNBQWMsQ0FBRSxTQUF5QjtRQUN4QyxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7UUFDdkIsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBQ3ZELEVBQUUsQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLFNBQVMsQ0FBQyxPQUFPLEVBQUUsT0FBTyxDQUFDLENBQUM7UUFDdkQsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOztPQUVHO0lBQ0gsdUJBQXVCLENBQUUsU0FBeUI7UUFDakQsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1FBQ3ZCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxZQUFZLENBQUMsQ0FBQztRQUN6RCxFQUFFLENBQUMsYUFBYSxDQUFDLFFBQVEsRUFBRSxTQUFTLENBQUMsT0FBTyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ3ZELE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7SUFFRDs7T0FFRztJQUNILE9BQU8sQ0FBRSxRQUFnQixFQUFFLE9BQWU7UUFDekMs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V0FBVyxFQUFHLElBQUksSUFBSSxFQUFFLENBQUMsV0FBVyxFQUFFO1lBQ3RDLE1BQU0sRUFBUSxTQUFTO1lBQ3ZCLFNBQVM7U0FDVCxDQUFDO1FBRUYsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ25FLE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7SUFFRDs7T0FFRztJQUNILGtCQUFrQixDQUFFLEtBQXNCO1FBQ3pDLElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztRQUN2QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsZ0JBQWdCLENBQUMsQ0FBQztRQUU3RCxNQUFNLElBQUksR0FBa0I7WUFDM0IsT0FBTyxFQUFPLEtBQUs7WUFDbkIsV0FBVyxFQUFHLElBQUksSUFBSSxFQUFFLENBQUMsV0FBVyxFQUFFO1lBQ3RDLEtBQUs7U0FDTCxDQUFDO1FBRUYsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ25FLE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7Q0FDRDtBQTNQRCxrQ0EyUEMiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIGZzIGZyb20gJ2ZzJztcbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQge1xuXHRHZW5lcmF0ZWRUeXBlcywgRGVmaW5pdGlvbkluZm8sIFVzYWdlSW5mbywgRURTSW5mbywgRmxvd0luZm8sIEZsb3dKc29uLCBIaWVyYXJjaHlOb2RlLCBIaWVyYXJjaHlKc29uLFxuXHRJbnN0cnVtZW50YXRpb25Qb2ludCwgSW5zdHJ1bWVudGF0aW9uSnNvbiwgTW9kdWxlR3JhcGgsIE1vZHVsZXNKc29uLCBTY29wZUFuYWx5c2lzLCBTY29wZXNKc29uLCBDcmVhdGlvbkdyYXBoXG59IGZyb20gJy4vdHlwZXMnO1xuXG4vKipcbiAqIFdyaXRlcyBnZW5lcmF0ZWQgdHlwZXMgdG8gZmlsZSBzeXN0ZW1cbiAqL1xuZXhwb3J0IGNsYXNzIFR5cGVzV3JpdGVyIHtcblx0cHJpdmF0ZSBvdXRwdXREaXI6IHN0cmluZztcblxuXHRjb25zdHJ1Y3RvciAob3V0cHV0RGlyID0gJy50YWN0aWNhJykge1xuXHRcdHRoaXMub3V0cHV0RGlyID0gb3V0cHV0RGlyO1xuXHR9XG5cblx0LyoqXG5cdCAqIExlZ2FjeSB3cml0ZSBtZXRob2QgLSBkZWxlZ2F0ZXMgdG8gd3JpdGVUeXBlc0ZpbGVcblx0ICovXG5cdHdyaXRlIChnZW5lcmF0ZWQ6IEdlbmVyYXRlZFR5cGVzKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gdGhpcy53cml0ZVR5cGVzRmlsZShnZW5lcmF0ZWQpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHR5cGVzLnRzIGZpbGUgKGV4cG9ydGFibGUgdHlwZSBhbGlhc2VzIC0gZGVmYXVsdCBtb2RlKVxuXHQgKi9cblx0d3JpdGVUeXBlc0ZpbGUgKGdlbmVyYXRlZDogR2VuZXJhdGVkVHlwZXMpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICd0eXBlcy50cycpO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIGdlbmVyYXRlZC5jb250ZW50LCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgZ2xvYmFsIGF1Z21lbnRhdGlvbiBmaWxlIChpbmRleC5kLnRzIC0gbW9kdWxlIGF1Z21lbnRhdGlvbiBtb2RlKVxuXHQgKi9cblx0d3JpdGVHbG9iYWxBdWdtZW50YXRpb24gKGdlbmVyYXRlZDogR2VuZXJhdGVkVHlwZXMpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdpbmRleC5kLnRzJyk7XG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgZ2VuZXJhdGVkLmNvbnRlbnQsICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB0byBhIGN1c3RvbSBmaWxlbmFtZVxuXHQgKi9cblx0d3JpdGVUbyAoZmlsZW5hbWU6IHN0cmluZywgY29udGVudDogc3RyaW5nKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCBmaWxlbmFtZSk7XG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgY29udGVudCwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIEVuc3VyZSBvdXRwdXQgZGlyZWN0b3J5IGV4aXN0c1xuXHQgKi9cblx0cHJpdmF0ZSBlbnN1cmVEaXJlY3RvcnkgKCk6IHZvaWQge1xuXHRcdGlmICghZnMuZXhpc3RzU3luYyh0aGlzLm91dHB1dERpcikpIHtcblx0XHRcdGZzLm1rZGlyU3luYyh0aGlzLm91dHB1dERpciwgeyByZWN1cnNpdmUgOiB0cnVlIH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDbGVhbiB0aGUgb3V0cHV0IGRpcmVjdG9yeVxuXHQgKi9cblx0Y2xlYW4gKCk6IHZvaWQge1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKHRoaXMub3V0cHV0RGlyKSkge1xuXHRcdFx0Y29uc3QgZmlsZXMgPSBmcy5yZWFkZGlyU3luYyh0aGlzLm91dHB1dERpcik7XG5cdFx0XHRmb3IgKGNvbnN0IGZpbGUgb2YgZmlsZXMpIHtcblx0XHRcdFx0ZnMudW5saW5rU3luYyhwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsIGZpbGUpKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogR2V0IG91dHB1dCBkaXJlY3Rvcnlcblx0ICovXG5cdGdldE91dHB1dERpciAoKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gdGhpcy5vdXRwdXREaXI7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgZGVmaW5pdGlvbnMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZURlZmluaXRpb25zRmlsZSAoZGVmaW5pdGlvbnM6IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPik6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2RlZmluaXRpb25zLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwIHRvIHBsYWluIG9iamVjdFxuXHRcdGNvbnN0IGRlZmluaXRpb25zT2JqOiBSZWNvcmQ8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGRlZmluaXRpb25zKSB7XG5cdFx0XHRkZWZpbml0aW9uc09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uID0ge1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0ZGVmaW5pdGlvbnMgOiBkZWZpbml0aW9uc09iaixcblx0XHR9O1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB1c2FnZXMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZVVzYWdlc0ZpbGUgKHVzYWdlczogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+KTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAndXNhZ2VzLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwIHRvIHBsYWluIG9iamVjdFxuXHRcdGNvbnN0IHVzYWdlc09iajogUmVjb3JkPHN0cmluZywgVXNhZ2VJbmZvW10+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiB1c2FnZXMpIHtcblx0XHRcdHVzYWdlc09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uID0ge1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0dXNhZ2VzICAgICAgOiB1c2FnZXNPYmosXG5cdFx0fTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgZWRzLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVFRFNGaWxlIChlZHM6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdlZHMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZWRzT2JqOiBSZWNvcmQ8c3RyaW5nLCBFRFNJbmZvW10+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBlZHMpIHtcblx0XHRcdGVkc09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uID0ge1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0ZWRzICAgICAgICAgOiBlZHNPYmosXG5cdFx0fTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgaW5zdHJ1bWVudGF0aW9uLmpzb24gZmlsZSAodjI6IGFkZHMgdGhlIGNyZWF0aW9uR3JhcGgga2V5IHdoZW5cblx0ICogdGhlIGNhbGxlciBwYXNzZXMgY3JlYXRpb24tZ3JhcGggZGF0YSDigJQgdGhlIENMSSBhbHdheXMgZG9lcylcblx0ICovXG5cdHdyaXRlSW5zdHJ1bWVudGF0aW9uRmlsZSAocG9pbnRzOiBJbnN0cnVtZW50YXRpb25Qb2ludFtdLCBjcmVhdGlvbkdyYXBoPzogQ3JlYXRpb25HcmFwaCk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2luc3RydW1lbnRhdGlvbi5qc29uJyk7XG5cblx0XHRjb25zdCBqc29uOiBJbnN0cnVtZW50YXRpb25Kc29uID0ge1xuXHRcdFx0dmVyc2lvbiAgICAgOiAyLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRwb2ludHMsXG5cdFx0fTtcblx0XHRpZiAoY3JlYXRpb25HcmFwaCkge1xuXHRcdFx0anNvbi5jcmVhdGlvbkdyYXBoID0gY3JlYXRpb25HcmFwaDtcblx0XHR9XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGZsb3cuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZUZsb3dGaWxlIChmbG93OiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPik6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2Zsb3cuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZmxvd09iajogUmVjb3JkPHN0cmluZywgRmxvd0luZm9bXT4gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGZsb3cpIHtcblx0XHRcdGZsb3dPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbjogRmxvd0pzb24gPSB7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRmbG93ICAgICAgICA6IGZsb3dPYmosXG5cdFx0fTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgbW9kdWxlcy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlTW9kdWxlc0ZpbGUgKGdyYXBoOiBNb2R1bGVHcmFwaCk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ21vZHVsZXMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgbW9kdWxlc09iajogTW9kdWxlc0pzb25bICdtb2R1bGVzJyBdID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBncmFwaC5tb2R1bGVzKSB7XG5cdFx0XHRtb2R1bGVzT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGpzb246IE1vZHVsZXNKc29uID0ge1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0bW9kdWxlcyAgICAgOiBtb2R1bGVzT2JqLFxuXHRcdFx0ZWRnZXMgICAgICAgOiBncmFwaC5lZGdlcyxcblx0XHRcdGN5Y2xlcyAgICAgIDogZ3JhcGguY3ljbGVzLFxuXHRcdH07XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHNjb3Blcy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlU2NvcGVzRmlsZSAoYW5hbHlzaXM6IFNjb3BlQW5hbHlzaXMpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdzY29wZXMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXBzIHRvIHBsYWluIHNoYXBlc1xuXHRcdGNvbnN0IHNjb3Blc09iajogU2NvcGVzSnNvblsgJ3Njb3BlcycgXSA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgYW5hbHlzaXMuc2NvcGVzKSB7XG5cdFx0XHRzY29wZXNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXHRcdGNvbnN0IHZhcmlhYmxlcyA9IEFycmF5LmZyb20oYW5hbHlzaXMudmFyaWFibGVzLnZhbHVlcygpKTtcblxuXHRcdGNvbnN0IGpzb246IFNjb3Blc0pzb24gPSB7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRzY29wZXMgICAgICA6IHNjb3Blc09iaixcblx0XHRcdHZhcmlhYmxlcyxcblx0XHR9O1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBoaWVyYXJjaHkuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZUhpZXJhcmNoeUZpbGUgKHJvb3RzOiBIaWVyYXJjaHlOb2RlW10pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdoaWVyYXJjaHkuanNvbicpO1xuXG5cdFx0Y29uc3QganNvbjogSGllcmFyY2h5SnNvbiA9IHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdHJvb3RzLFxuXHRcdH07XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG59XG4iXX0=