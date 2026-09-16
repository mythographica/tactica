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
    constructor(outputDir = '.tactica', projectRoot) {
        this.outputDir = outputDir;
        this.projectRoot = projectRoot === undefined
            ? undefined
            : path.resolve(projectRoot);
    }
    /**
     * Rewrite every project-rooted absolute path in the payload to a
     * project-relative one (values AND object keys), so .tactica output
     * stays portable across machines and checkouts. Paths outside the
     * project root keep their absolute form — they genuinely are
     * machine-specific. Consumers resolve relative entries against the
     * directory that holds .tactica.
     */
    relativize(payload) {
        if (this.projectRoot === undefined) {
            return payload;
        }
        const prefix = this.projectRoot + path.sep;
        const walk = (input) => {
            if (typeof input === 'string') {
                if (!input.startsWith(prefix)) {
                    return input;
                }
                const relative = input.slice(prefix.length);
                const walked = relative.split(path.sep).join('/');
                return walked;
            }
            if (Array.isArray(input)) {
                const walked = input.map(walk);
                return walked;
            }
            if (input !== null && typeof input === 'object') {
                const walked = {};
                for (const [key, value] of Object.entries(input)) {
                    const walkedKey = walk(key);
                    walked[walkedKey] = walk(value);
                }
                return walked;
            }
            return input;
        };
        const result = walk(payload);
        return result;
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
        const json = this.relativize({
            version: '1.0',
            generatedAt: new Date().toISOString(),
            definitions: definitionsObj,
        });
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
        const json = this.relativize({
            version: '1.0',
            generatedAt: new Date().toISOString(),
            usages: usagesObj,
        });
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
        const json = this.relativize({
            version: '1.0',
            generatedAt: new Date().toISOString(),
            eds: edsObj,
        });
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
        const relativized = this.relativize(json);
        fs.writeFileSync(filePath, JSON.stringify(relativized, null, 2), 'utf-8');
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
        const json = this.relativize({
            version: '1.0',
            generatedAt: new Date().toISOString(),
            flow: flowObj,
        });
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
        const json = this.relativize({
            version: '1.0',
            generatedAt: new Date().toISOString(),
            modules: modulesObj,
            edges: graph.edges,
            cycles: graph.cycles,
        });
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
        const json = this.relativize({
            version: '1.0',
            generatedAt: new Date().toISOString(),
            scopes: scopesObj,
            variables,
        });
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write hierarchy.json file
     */
    writeHierarchyFile(roots) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'hierarchy.json');
        const json = this.relativize({
            version: '1.0',
            generatedAt: new Date().toISOString(),
            roots,
        });
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
}
exports.TypesWriter = TypesWriter;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoid3JpdGVyLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL3dyaXRlci50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLHVDQUF5QjtBQUN6QiwyQ0FBNkI7QUFNN0I7O0dBRUc7QUFDSCxNQUFhLFdBQVc7SUFJdkIsWUFBYSxTQUFTLEdBQUcsVUFBVSxFQUFFLFdBQW9CO1FBQ3hELElBQUksQ0FBQyxTQUFTLEdBQUcsU0FBUyxDQUFDO1FBQzNCLElBQUksQ0FBQyxXQUFXLEdBQUcsV0FBVyxLQUFLLFNBQVM7WUFDM0MsQ0FBQyxDQUFDLFNBQVM7WUFDWCxDQUFDLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxXQUFXLENBQUMsQ0FBQztJQUM5QixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLFVBQVUsQ0FBSyxPQUFVO1FBQ2hDLElBQUksSUFBSSxDQUFDLFdBQVcsS0FBSyxTQUFTLEVBQUUsQ0FBQztZQUNwQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFdBQVcsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO1FBQzNDLE1BQU0sSUFBSSxHQUFHLENBQUMsS0FBYyxFQUFXLEVBQUU7WUFDeEMsSUFBSSxPQUFPLEtBQUssS0FBSyxRQUFRLEVBQUUsQ0FBQztnQkFDL0IsSUFBSSxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztvQkFDL0IsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztnQkFDRCxNQUFNLFFBQVEsR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQztnQkFDNUMsTUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxD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QUMsQ0FBQztRQUU3RCxNQUFNLElBQUksR0FBa0IsSUFBSSxDQUFDLFVBQVUsQ0FBQztZQUMzQyxPQUFPLEVBQU8sS0FBSztZQUNuQixXQUFXLEVBQUcsSUFBSSxJQUFJLEVBQUUsQ0FBQyxXQUFXLEVBQUU7WUFDdEMsS0FBSztTQUNMLENBQUMsQ0FBQztRQUVILEVBQUUsQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxDQUFDLENBQUMsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUNuRSxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0NBQ0Q7QUF4U0Qsa0NBd1NDIiwic291cmNlc0NvbnRlbnQiOlsiJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBmcyBmcm9tICdmcyc7XG5pbXBvcnQgKiBhcyBwYXRoIGZyb20gJ3BhdGgnO1xuaW1wb3J0IHtcblx0R2VuZXJhdGVkVHlwZXMsIERlZmluaXRpb25JbmZvLCBVc2FnZUluZm8sIEVEU0luZm8sIEZsb3dJbmZvLCBGbG93SnNvbiwgSGllcmFyY2h5Tm9kZSwgSGllcmFyY2h5SnNvbixcblx0SW5zdHJ1bWVudGF0aW9uUG9pbnQsIEluc3RydW1lbnRhdGlvbkpzb24sIE1vZHVsZUdyYXBoLCBNb2R1bGVzSnNvbiwgU2NvcGVBbmFseXNpcywgU2NvcGVzSnNvbiwgQ3JlYXRpb25HcmFwaFxufSBmcm9tICcuL3R5cGVzJztcblxuLyoqXG4gKiBXcml0ZXMgZ2VuZXJhdGVkIHR5cGVzIHRvIGZpbGUgc3lzdGVtXG4gKi9cbmV4cG9ydCBjbGFzcyBUeXBlc1dyaXRlciB7XG5cdHByaXZhdGUgb3V0cHV0RGlyOiBzdHJpbmc7XG5cdHByaXZhdGUgcHJvamVjdFJvb3Q/OiBzdHJpbmc7XG5cblx0Y29uc3RydWN0b3IgKG91dHB1dERpciA9ICcudGFjdGljYScsIHByb2plY3RSb290Pzogc3RyaW5nKSB7XG5cdFx0dGhpcy5vdXRwdXREaXIgPSBvdXRwdXREaXI7XG5cdFx0dGhpcy5wcm9qZWN0Um9vdCA9IHByb2plY3RSb290ID09PSB1bmRlZmluZWRcblx0XHRcdD8gdW5kZWZpbmVkXG5cdFx0XHQ6IHBhdGgucmVzb2x2ZShwcm9qZWN0Um9vdCk7XG5cdH1cblxuXHQvKipcblx0ICogUmV3cml0ZSBldmVyeSBwcm9qZWN0LXJvb3RlZCBhYnNvbHV0ZSBwYXRoIGluIHRoZSBwYXlsb2FkIHRvIGFcblx0ICogcHJvamVjdC1yZWxhdGl2ZSBvbmUgKHZhbHVlcyBBTkQgb2JqZWN0IGtleXMpLCBzbyAudGFjdGljYSBvdXRwdXRcblx0ICogc3RheXMgcG9ydGFibGUgYWNyb3NzIG1hY2hpbmVzIGFuZCBjaGVja291dHMuIFBhdGhzIG91dHNpZGUgdGhlXG5cdCAqIHByb2plY3Qgcm9vdCBrZWVwIHRoZWlyIGFic29sdXRlIGZvcm0g4oCUIHRoZXkgZ2VudWluZWx5IGFyZVxuXHQgKiBtYWNoaW5lLXNwZWNpZmljLiBDb25zdW1lcnMgcmVzb2x2ZSByZWxhdGl2ZSBlbnRyaWVzIGFnYWluc3QgdGhlXG5cdCAqIGRpcmVjdG9yeSB0aGF0IGhvbGRzIC50YWN0aWNhLlxuXHQgKi9cblx0cHJpdmF0ZSByZWxhdGl2aXplPFQ+IChwYXlsb2FkOiBUKTogVCB7XG5cdFx0aWYgKHRoaXMucHJvamVjdFJvb3QgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0cmV0dXJuIHBheWxvYWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHByZWZpeCA9IHRoaXMucHJvamVjdFJvb3QgKyBwYXRoLnNlcDtcblx0XHRjb25zdCB3YWxrID0gKGlucHV0OiB1bmtub3duKTogdW5rbm93biA9PiB7XG5cdFx0XHRpZiAodHlwZW9mIGlucHV0ID09PSAnc3RyaW5nJykge1xuXHRcdFx0XHRpZiAoIWlucHV0LnN0YXJ0c1dpdGgocHJlZml4KSkge1xuXHRcdFx0XHRcdHJldHVybiBpbnB1dDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCByZWxhdGl2ZSA9IGlucHV0LnNsaWNlKHByZWZpeC5sZW5ndGgpO1xuXHRcdFx0XHRjb25zdCB3YWxrZWQgPSByZWxhdGl2ZS5zcGxpdChwYXRoLnNlcCkuam9pbignLycpO1xuXHRcdFx0XHRyZXR1cm4gd2Fsa2VkO1xuXHRcdFx0fVxuXHRcdFx0aWYgKEFycmF5LmlzQXJyYXkoaW5wdXQpKSB7XG5cdFx0XHRcdGNvbnN0IHdhbGtlZCA9IGlucHV0Lm1hcCh3YWxrKTtcblx0XHRcdFx0cmV0dXJuIHdhbGtlZDtcblx0XHRcdH1cblx0XHRcdGlmIChpbnB1dCAhPT0gbnVsbCAmJiB0eXBlb2YgaW5wdXQgPT09ICdvYmplY3QnKSB7XG5cdFx0XHRcdGNvbnN0IHdhbGtlZDogUmVjb3JkPHN0cmluZywgdW5rbm93bj4gPSB7fTtcblx0XHRcdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBPYmplY3QuZW50cmllcyhpbnB1dCkpIHtcblx0XHRcdFx0XHRjb25zdCB3YWxrZWRLZXkgPSB3YWxrKGtleSkgYXMgc3RyaW5nO1xuXHRcdFx0XHRcdHdhbGtlZFsgd2Fsa2VkS2V5IF0gPSB3YWxrKHZhbHVlKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gd2Fsa2VkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGlucHV0O1xuXHRcdH07XG5cdFx0Y29uc3QgcmVzdWx0ID0gd2FsayhwYXlsb2FkKTtcblx0XHRyZXR1cm4gcmVzdWx0IGFzIFQ7XG5cdH1cblxuXHQvKipcblx0ICogTGVnYWN5IHdyaXRlIG1ldGhvZCAtIGRlbGVnYXRlcyB0byB3cml0ZVR5cGVzRmlsZVxuXHQgKi9cblx0d3JpdGUgKGdlbmVyYXRlZDogR2VuZXJhdGVkVHlwZXMpOiBzdHJpbmcge1xuXHRcdHJldHVybiB0aGlzLndyaXRlVHlwZXNGaWxlKGdlbmVyYXRlZCk7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgdHlwZXMudHMgZmlsZSAoZXhwb3J0YWJsZSB0eXBlIGFsaWFzZXMgLSBkZWZhdWx0IG1vZGUpXG5cdCAqL1xuXHR3cml0ZVR5cGVzRmlsZSAoZ2VuZXJhdGVkOiBHZW5lcmF0ZWRUeXBlcyk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ3R5cGVzLnRzJyk7XG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgZ2VuZXJhdGVkLmNvbnRlbnQsICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBnbG9iYWwgYXVnbWVudGF0aW9uIGZpbGUgKGluZGV4LmQudHMgLSBtb2R1bGUgYXVnbWVudGF0aW9uIG1vZGUpXG5cdCAqL1xuXHR3cml0ZUdsb2JhbEF1Z21lbnRhdGlvbiAoZ2VuZXJhdGVkOiBHZW5lcmF0ZWRUeXBlcyk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2luZGV4LmQudHMnKTtcblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBnZW5lcmF0ZWQuY29udGVudCwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHRvIGEgY3VzdG9tIGZpbGVuYW1lXG5cdCAqL1xuXHR3cml0ZVRvIChmaWxlbmFtZTogc3RyaW5nLCBjb250ZW50OiBzdHJpbmcpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsIGZpbGVuYW1lKTtcblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBjb250ZW50LCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogRW5zdXJlIG91dHB1dCBkaXJlY3RvcnkgZXhpc3RzXG5cdCAqL1xuXHRwcml2YXRlIGVuc3VyZURpcmVjdG9yeSAoKTogdm9pZCB7XG5cdFx0aWYgKCFmcy5leGlzdHNTeW5jKHRoaXMub3V0cHV0RGlyKSkge1xuXHRcdFx0ZnMubWtkaXJTeW5jKHRoaXMub3V0cHV0RGlyLCB7IHJlY3Vyc2l2ZSA6IHRydWUgfSk7XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIENsZWFuIHRoZSBvdXRwdXQgZGlyZWN0b3J5XG5cdCAqL1xuXHRjbGVhbiAoKTogdm9pZCB7XG5cdFx0aWYgKGZzLmV4aXN0c1N5bmModGhpcy5vdXRwdXREaXIpKSB7XG5cdFx0XHRjb25zdCBmaWxlcyA9IGZzLnJlYWRkaXJTeW5jKHRoaXMub3V0cHV0RGlyKTtcblx0XHRcdGZvciAoY29uc3QgZmlsZSBvZiBmaWxlcykge1xuXHRcdFx0XHRmcy51bmxpbmtTeW5jKHBhdGguam9pbih0aGlzLm91dHB1dERpciwgZmlsZSkpO1xuXHRcdFx0fVxuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgb3V0cHV0IGRpcmVjdG9yeVxuXHQgKi9cblx0Z2V0T3V0cHV0RGlyICgpOiBzdHJpbmcge1xuXHRcdHJldHVybiB0aGlzLm91dHB1dERpcjtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBkZWZpbml0aW9ucy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlRGVmaW5pdGlvbnNGaWxlIChkZWZpbml0aW9uczogTWFwPHN0cmluZywgRGVmaW5pdGlvbkluZm8+KTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnZGVmaW5pdGlvbnMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZGVmaW5pdGlvbnNPYmo6IFJlY29yZDxzdHJpbmcsIERlZmluaXRpb25JbmZvPiA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRcdGRlZmluaXRpb25zT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGpzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0ZGVmaW5pdGlvbnMgOiBkZWZpbml0aW9uc09iaixcblx0XHR9KTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgdXNhZ2VzLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVVc2FnZXNGaWxlICh1c2FnZXM6IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPik6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ3VzYWdlcy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCB1c2FnZXNPYmo6IFJlY29yZDxzdHJpbmcsIFVzYWdlSW5mb1tdPiA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgdXNhZ2VzKSB7XG5cdFx0XHR1c2FnZXNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHR1c2FnZXMgICAgICA6IHVzYWdlc09iaixcblx0XHR9KTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgZWRzLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVFRFNGaWxlIChlZHM6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdlZHMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZWRzT2JqOiBSZWNvcmQ8c3RyaW5nLCBFRFNJbmZvW10+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBlZHMpIHtcblx0XHRcdGVkc09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdGVkcyAgICAgICAgIDogZWRzT2JqLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBpbnN0cnVtZW50YXRpb24uanNvbiBmaWxlICh2MjogYWRkcyB0aGUgY3JlYXRpb25HcmFwaCBrZXkgd2hlblxuXHQgKiB0aGUgY2FsbGVyIHBhc3NlcyBjcmVhdGlvbi1ncmFwaCBkYXRhIOKAlCB0aGUgQ0xJIGFsd2F5cyBkb2VzKVxuXHQgKi9cblx0d3JpdGVJbnN0cnVtZW50YXRpb25GaWxlIChwb2ludHM6IEluc3RydW1lbnRhdGlvblBvaW50W10sIGNyZWF0aW9uR3JhcGg/OiBDcmVhdGlvbkdyYXBoKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnaW5zdHJ1bWVudGF0aW9uLmpzb24nKTtcblxuXHRcdGNvbnN0IGpzb246IEluc3RydW1lbnRhdGlvbkpzb24gPSB7XG5cdFx0XHR2ZXJzaW9uICAgICA6IDIsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdHBvaW50cyxcblx0XHR9O1xuXHRcdGlmIChjcmVhdGlvbkdyYXBoKSB7XG5cdFx0XHRqc29uLmNyZWF0aW9uR3JhcGggPSBjcmVhdGlvbkdyYXBoO1xuXHRcdH1cblxuXHRcdGNvbnN0IHJlbGF0aXZpemVkID0gdGhpcy5yZWxhdGl2aXplKGpzb24pO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KHJlbGF0aXZpemVkLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGZsb3cuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZUZsb3dGaWxlIChmbG93OiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPik6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2Zsb3cuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZmxvd09iajogUmVjb3JkPHN0cmluZywgRmxvd0luZm9bXT4gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGZsb3cpIHtcblx0XHRcdGZsb3dPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbjogRmxvd0pzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0ZmxvdyAgICAgICAgOiBmbG93T2JqLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBtb2R1bGVzLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVNb2R1bGVzRmlsZSAoZ3JhcGg6IE1vZHVsZUdyYXBoKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnbW9kdWxlcy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBtb2R1bGVzT2JqOiBNb2R1bGVzSnNvblsgJ21vZHVsZXMnIF0gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGdyYXBoLm1vZHVsZXMpIHtcblx0XHRcdG1vZHVsZXNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbjogTW9kdWxlc0pzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0bW9kdWxlcyAgICAgOiBtb2R1bGVzT2JqLFxuXHRcdFx0ZWRnZXMgICAgICAgOiBncmFwaC5lZGdlcyxcblx0XHRcdGN5Y2xlcyAgICAgIDogZ3JhcGguY3ljbGVzLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBzY29wZXMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZVNjb3Blc0ZpbGUgKGFuYWx5c2lzOiBTY29wZUFuYWx5c2lzKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnc2NvcGVzLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwcyB0byBwbGFpbiBzaGFwZXNcblx0XHRjb25zdCBzY29wZXNPYmo6IFNjb3Blc0pzb25bICdzY29wZXMnIF0gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGFuYWx5c2lzLnNjb3Blcykge1xuXHRcdFx0c2NvcGVzT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblx0XHRjb25zdCB2YXJpYWJsZXMgPSBBcnJheS5mcm9tKGFuYWx5c2lzLnZhcmlhYmxlcy52YWx1ZXMoKSk7XG5cblx0XHRjb25zdCBqc29uOiBTY29wZXNKc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdHNjb3BlcyAgICAgIDogc2NvcGVzT2JqLFxuXHRcdFx0dmFyaWFibGVzLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBoaWVyYXJjaHkuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZUhpZXJhcmNoeUZpbGUgKHJvb3RzOiBIaWVyYXJjaHlOb2RlW10pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdoaWVyYXJjaHkuanNvbicpO1xuXG5cdFx0Y29uc3QganNvbjogSGllcmFyY2h5SnNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRyb290cyxcblx0XHR9KTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cbn1cbiJdfQ==