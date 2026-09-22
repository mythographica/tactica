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
    /**
     * Write the collection manifest: one entry per collection (default
     * first when default-collection types exist), ids + display names +
     * Option-B registry interfaces + call sites. The id↔interface mapping
     * is the join key between the `collectionId::`-prefixed graph outputs
     * and the registry-prefixed aliases in types.ts / registry.ts.
     */
    writeCollectionsFile(collections) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'collections.json');
        const json = this.relativize({
            version: '1.0',
            generatedAt: new Date().toISOString(),
            collections,
        });
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
}
exports.TypesWriter = TypesWriter;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoid3JpdGVyLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL3dyaXRlci50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLHVDQUF5QjtBQUN6QiwyQ0FBNkI7QUFPN0I7O0dBRUc7QUFDSCxNQUFhLFdBQVc7SUFJdkIsWUFBYSxTQUFTLEdBQUcsVUFBVSxFQUFFLFdBQW9CO1FBQ3hELElBQUksQ0FBQyxTQUFTLEdBQUcsU0FBUyxDQUFDO1FBQzNCLElBQUksQ0FBQyxXQUFXLEdBQUcsV0FBVyxLQUFLLFNBQVM7WUFDM0MsQ0FBQyxDQUFDLFNBQVM7WUFDWCxDQUFDLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxXQUFXLENBQUMsQ0FBQztJQUM5QixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLFVBQVUsQ0FBSyxPQUFVO1FBQ2hDLElBQUksSUFBSSxDQUFDLFdBQVcsS0FBSyxTQUFTLEVBQUUsQ0FBQztZQUNwQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFdBQVcsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO1FBQzNDLE1BQU0sSUFBSSxHQUFHLENBQUMsS0FBYyxFQUFXLEVBQUU7WUFDeEMsSUFBSSxPQUFPLEtBQUssS0FBSyxRQUFRLEVBQUUsQ0FBQztnQkFDL0IsSUFBSSxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztvQkFDL0IsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztnQkFDRCxNQUFNLFFBQVEsR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQztnQkFDNUMsTUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxD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QUMsQ0FBQztRQUU3RCxNQUFNLElBQUksR0FBa0IsSUFBSSxDQUFDLFVBQVUsQ0FBQztZQUMzQyxPQUFPLEVBQU8sS0FBSztZQUNuQixXQUFXLEVBQUcsSUFBSSxJQUFJLEVBQUUsQ0FBQyxXQUFXLEVBQUU7WUFDdEMsS0FBSztTQUNMLENBQUMsQ0FBQztRQUVILEVBQUUsQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxDQUFDLENBQUMsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUNuRSxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0gsb0JBQW9CLENBQUUsV0FBc0M7UUFDM0QsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1FBQ3ZCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxrQkFBa0IsQ0FBQyxDQUFDO1FBRS9ELE1BQU0sSUFBSSxHQUFvQixJQUFJLENBQUMsVUFBVSxDQUFDO1lBQzdDLE9BQU8sRUFBTyxLQUFLO1lBQ25CLFdBQVcsRUFBRyxJQUFJLElBQUksRUFBRSxDQUFDLFdBQVcsRUFBRTtZQUN0QyxXQUFXO1NBQ1gsQ0FBQyxDQUFDO1FBRUgsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ25FLE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7Q0FDRDtBQTdURCxrQ0E2VEMiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIGZzIGZyb20gJ2ZzJztcbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQge1xuXHRHZW5lcmF0ZWRUeXBlcywgRGVmaW5pdGlvbkluZm8sIFVzYWdlSW5mbywgRURTSW5mbywgRmxvd0luZm8sIEZsb3dKc29uLCBIaWVyYXJjaHlOb2RlLCBIaWVyYXJjaHlKc29uLFxuXHRJbnN0cnVtZW50YXRpb25Qb2ludCwgSW5zdHJ1bWVudGF0aW9uSnNvbiwgTW9kdWxlR3JhcGgsIE1vZHVsZXNKc29uLCBTY29wZUFuYWx5c2lzLCBTY29wZXNKc29uLCBDcmVhdGlvbkdyYXBoLFxuXHRDb2xsZWN0aW9uTWFuaWZlc3RFbnRyeSwgQ29sbGVjdGlvbnNKc29uXG59IGZyb20gJy4vdHlwZXMnO1xuXG4vKipcbiAqIFdyaXRlcyBnZW5lcmF0ZWQgdHlwZXMgdG8gZmlsZSBzeXN0ZW1cbiAqL1xuZXhwb3J0IGNsYXNzIFR5cGVzV3JpdGVyIHtcblx0cHJpdmF0ZSBvdXRwdXREaXI6IHN0cmluZztcblx0cHJpdmF0ZSBwcm9qZWN0Um9vdD86IHN0cmluZztcblxuXHRjb25zdHJ1Y3RvciAob3V0cHV0RGlyID0gJy50YWN0aWNhJywgcHJvamVjdFJvb3Q/OiBzdHJpbmcpIHtcblx0XHR0aGlzLm91dHB1dERpciA9IG91dHB1dERpcjtcblx0XHR0aGlzLnByb2plY3RSb290ID0gcHJvamVjdFJvb3QgPT09IHVuZGVmaW5lZFxuXHRcdFx0PyB1bmRlZmluZWRcblx0XHRcdDogcGF0aC5yZXNvbHZlKHByb2plY3RSb290KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXdyaXRlIGV2ZXJ5IHByb2plY3Qtcm9vdGVkIGFic29sdXRlIHBhdGggaW4gdGhlIHBheWxvYWQgdG8gYVxuXHQgKiBwcm9qZWN0LXJlbGF0aXZlIG9uZSAodmFsdWVzIEFORCBvYmplY3Qga2V5cyksIHNvIC50YWN0aWNhIG91dHB1dFxuXHQgKiBzdGF5cyBwb3J0YWJsZSBhY3Jvc3MgbWFjaGluZXMgYW5kIGNoZWNrb3V0cy4gUGF0aHMgb3V0c2lkZSB0aGVcblx0ICogcHJvamVjdCByb290IGtlZXAgdGhlaXIgYWJzb2x1dGUgZm9ybSDigJQgdGhleSBnZW51aW5lbHkgYXJlXG5cdCAqIG1hY2hpbmUtc3BlY2lmaWMuIENvbnN1bWVycyByZXNvbHZlIHJlbGF0aXZlIGVudHJpZXMgYWdhaW5zdCB0aGVcblx0ICogZGlyZWN0b3J5IHRoYXQgaG9sZHMgLnRhY3RpY2EuXG5cdCAqL1xuXHRwcml2YXRlIHJlbGF0aXZpemU8VD4gKHBheWxvYWQ6IFQpOiBUIHtcblx0XHRpZiAodGhpcy5wcm9qZWN0Um9vdCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRyZXR1cm4gcGF5bG9hZDtcblx0XHR9XG5cdFx0Y29uc3QgcHJlZml4ID0gdGhpcy5wcm9qZWN0Um9vdCArIHBhdGguc2VwO1xuXHRcdGNvbnN0IHdhbGsgPSAoaW5wdXQ6IHVua25vd24pOiB1bmtub3duID0+IHtcblx0XHRcdGlmICh0eXBlb2YgaW5wdXQgPT09ICdzdHJpbmcnKSB7XG5cdFx0XHRcdGlmICghaW5wdXQuc3RhcnRzV2l0aChwcmVmaXgpKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGlucHV0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IHJlbGF0aXZlID0gaW5wdXQuc2xpY2UocHJlZml4Lmxlbmd0aCk7XG5cdFx0XHRcdGNvbnN0IHdhbGtlZCA9IHJlbGF0aXZlLnNwbGl0KHBhdGguc2VwKS5qb2luKCcvJyk7XG5cdFx0XHRcdHJldHVybiB3YWxrZWQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAoQXJyYXkuaXNBcnJheShpbnB1dCkpIHtcblx0XHRcdFx0Y29uc3Qgd2Fsa2VkID0gaW5wdXQubWFwKHdhbGspO1xuXHRcdFx0XHRyZXR1cm4gd2Fsa2VkO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGlucHV0ICE9PSBudWxsICYmIHR5cGVvZiBpbnB1dCA9PT0gJ29iamVjdCcpIHtcblx0XHRcdFx0Y29uc3Qgd2Fsa2VkOiBSZWNvcmQ8c3RyaW5nLCB1bmtub3duPiA9IHt9O1xuXHRcdFx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIE9iamVjdC5lbnRyaWVzKGlucHV0KSkge1xuXHRcdFx0XHRcdGNvbnN0IHdhbGtlZEtleSA9IHdhbGsoa2V5KSBhcyBzdHJpbmc7XG5cdFx0XHRcdFx0d2Fsa2VkWyB3YWxrZWRLZXkgXSA9IHdhbGsodmFsdWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB3YWxrZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gaW5wdXQ7XG5cdFx0fTtcblx0XHRjb25zdCByZXN1bHQgPSB3YWxrKHBheWxvYWQpO1xuXHRcdHJldHVybiByZXN1bHQgYXMgVDtcblx0fVxuXG5cdC8qKlxuXHQgKiBMZWdhY3kgd3JpdGUgbWV0aG9kIC0gZGVsZWdhdGVzIHRvIHdyaXRlVHlwZXNGaWxlXG5cdCAqL1xuXHR3cml0ZSAoZ2VuZXJhdGVkOiBHZW5lcmF0ZWRUeXBlcyk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIHRoaXMud3JpdGVUeXBlc0ZpbGUoZ2VuZXJhdGVkKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB0eXBlcy50cyBmaWxlIChleHBvcnRhYmxlIHR5cGUgYWxpYXNlcyAtIGRlZmF1bHQgbW9kZSlcblx0ICovXG5cdHdyaXRlVHlwZXNGaWxlIChnZW5lcmF0ZWQ6IEdlbmVyYXRlZFR5cGVzKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAndHlwZXMudHMnKTtcblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBnZW5lcmF0ZWQuY29udGVudCwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGdsb2JhbCBhdWdtZW50YXRpb24gZmlsZSAoaW5kZXguZC50cyAtIG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZSlcblx0ICovXG5cdHdyaXRlR2xvYmFsQXVnbWVudGF0aW9uIChnZW5lcmF0ZWQ6IEdlbmVyYXRlZFR5cGVzKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnaW5kZXguZC50cycpO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIGdlbmVyYXRlZC5jb250ZW50LCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgdG8gYSBjdXN0b20gZmlsZW5hbWVcblx0ICovXG5cdHdyaXRlVG8gKGZpbGVuYW1lOiBzdHJpbmcsIGNvbnRlbnQ6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgZmlsZW5hbWUpO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIGNvbnRlbnQsICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbnN1cmUgb3V0cHV0IGRpcmVjdG9yeSBleGlzdHNcblx0ICovXG5cdHByaXZhdGUgZW5zdXJlRGlyZWN0b3J5ICgpOiB2b2lkIHtcblx0XHRpZiAoIWZzLmV4aXN0c1N5bmModGhpcy5vdXRwdXREaXIpKSB7XG5cdFx0XHRmcy5ta2RpclN5bmModGhpcy5vdXRwdXREaXIsIHsgcmVjdXJzaXZlIDogdHJ1ZSB9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ2xlYW4gdGhlIG91dHB1dCBkaXJlY3Rvcnlcblx0ICovXG5cdGNsZWFuICgpOiB2b2lkIHtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyh0aGlzLm91dHB1dERpcikpIHtcblx0XHRcdGNvbnN0IGZpbGVzID0gZnMucmVhZGRpclN5bmModGhpcy5vdXRwdXREaXIpO1xuXHRcdFx0Zm9yIChjb25zdCBmaWxlIG9mIGZpbGVzKSB7XG5cdFx0XHRcdGZzLnVubGlua1N5bmMocGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCBmaWxlKSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBvdXRwdXQgZGlyZWN0b3J5XG5cdCAqL1xuXHRnZXRPdXRwdXREaXIgKCk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIHRoaXMub3V0cHV0RGlyO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGRlZmluaXRpb25zLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVEZWZpbml0aW9uc0ZpbGUgKGRlZmluaXRpb25zOiBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdkZWZpbml0aW9ucy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBkZWZpbml0aW9uc09iajogUmVjb3JkPHN0cmluZywgRGVmaW5pdGlvbkluZm8+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdFx0ZGVmaW5pdGlvbnNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRkZWZpbml0aW9ucyA6IGRlZmluaXRpb25zT2JqLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB1c2FnZXMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZVVzYWdlc0ZpbGUgKHVzYWdlczogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+KTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAndXNhZ2VzLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwIHRvIHBsYWluIG9iamVjdFxuXHRcdGNvbnN0IHVzYWdlc09iajogUmVjb3JkPHN0cmluZywgVXNhZ2VJbmZvW10+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiB1c2FnZXMpIHtcblx0XHRcdHVzYWdlc09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdHVzYWdlcyAgICAgIDogdXNhZ2VzT2JqLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBlZHMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZUVEU0ZpbGUgKGVkczogTWFwPHN0cmluZywgRURTSW5mb1tdPik6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2Vkcy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBlZHNPYmo6IFJlY29yZDxzdHJpbmcsIEVEU0luZm9bXT4gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGVkcykge1xuXHRcdFx0ZWRzT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGpzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0ZWRzICAgICAgICAgOiBlZHNPYmosXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGluc3RydW1lbnRhdGlvbi5qc29uIGZpbGUgKHYyOiBhZGRzIHRoZSBjcmVhdGlvbkdyYXBoIGtleSB3aGVuXG5cdCAqIHRoZSBjYWxsZXIgcGFzc2VzIGNyZWF0aW9uLWdyYXBoIGRhdGEg4oCUIHRoZSBDTEkgYWx3YXlzIGRvZXMpXG5cdCAqL1xuXHR3cml0ZUluc3RydW1lbnRhdGlvbkZpbGUgKHBvaW50czogSW5zdHJ1bWVudGF0aW9uUG9pbnRbXSwgY3JlYXRpb25HcmFwaD86IENyZWF0aW9uR3JhcGgpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdpbnN0cnVtZW50YXRpb24uanNvbicpO1xuXG5cdFx0Y29uc3QganNvbjogSW5zdHJ1bWVudGF0aW9uSnNvbiA9IHtcblx0XHRcdHZlcnNpb24gICAgIDogMixcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0cG9pbnRzLFxuXHRcdH07XG5cdFx0aWYgKGNyZWF0aW9uR3JhcGgpIHtcblx0XHRcdGpzb24uY3JlYXRpb25HcmFwaCA9IGNyZWF0aW9uR3JhcGg7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVsYXRpdml6ZWQgPSB0aGlzLnJlbGF0aXZpemUoanNvbik7XG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkocmVsYXRpdml6ZWQsIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgZmxvdy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlRmxvd0ZpbGUgKGZsb3c6IE1hcDxzdHJpbmcsIEZsb3dJbmZvW10+KTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnZmxvdy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBmbG93T2JqOiBSZWNvcmQ8c3RyaW5nLCBGbG93SW5mb1tdPiA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgZmxvdykge1xuXHRcdFx0Zmxvd09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uOiBGbG93SnNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRmbG93ICAgICAgICA6IGZsb3dPYmosXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIG1vZHVsZXMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZU1vZHVsZXNGaWxlIChncmFwaDogTW9kdWxlR3JhcGgpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdtb2R1bGVzLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwIHRvIHBsYWluIG9iamVjdFxuXHRcdGNvbnN0IG1vZHVsZXNPYmo6IE1vZHVsZXNKc29uWyAnbW9kdWxlcycgXSA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgZ3JhcGgubW9kdWxlcykge1xuXHRcdFx0bW9kdWxlc09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uOiBNb2R1bGVzSnNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRtb2R1bGVzICAgICA6IG1vZHVsZXNPYmosXG5cdFx0XHRlZGdlcyAgICAgICA6IGdyYXBoLmVkZ2VzLFxuXHRcdFx0Y3ljbGVzICAgICAgOiBncmFwaC5jeWNsZXMsXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHNjb3Blcy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlU2NvcGVzRmlsZSAoYW5hbHlzaXM6IFNjb3BlQW5hbHlzaXMpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdzY29wZXMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXBzIHRvIHBsYWluIHNoYXBlc1xuXHRcdGNvbnN0IHNjb3Blc09iajogU2NvcGVzSnNvblsgJ3Njb3BlcycgXSA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgYW5hbHlzaXMuc2NvcGVzKSB7XG5cdFx0XHRzY29wZXNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXHRcdGNvbnN0IHZhcmlhYmxlcyA9IEFycmF5LmZyb20oYW5hbHlzaXMudmFyaWFibGVzLnZhbHVlcygpKTtcblxuXHRcdGNvbnN0IGpzb246IFNjb3Blc0pzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0c2NvcGVzICAgICAgOiBzY29wZXNPYmosXG5cdFx0XHR2YXJpYWJsZXMsXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGhpZXJhcmNoeS5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlSGllcmFyY2h5RmlsZSAocm9vdHM6IEhpZXJhcmNoeU5vZGVbXSk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2hpZXJhcmNoeS5qc29uJyk7XG5cblx0XHRjb25zdCBqc29uOiBIaWVyYXJjaHlKc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdHJvb3RzLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB0aGUgY29sbGVjdGlvbiBtYW5pZmVzdDogb25lIGVudHJ5IHBlciBjb2xsZWN0aW9uIChkZWZhdWx0XG5cdCAqIGZpcnN0IHdoZW4gZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzIGV4aXN0KSwgaWRzICsgZGlzcGxheSBuYW1lcyArXG5cdCAqIE9wdGlvbi1CIHJlZ2lzdHJ5IGludGVyZmFjZXMgKyBjYWxsIHNpdGVzLiBUaGUgaWTihpRpbnRlcmZhY2UgbWFwcGluZ1xuXHQgKiBpcyB0aGUgam9pbiBrZXkgYmV0d2VlbiB0aGUgYGNvbGxlY3Rpb25JZDo6YC1wcmVmaXhlZCBncmFwaCBvdXRwdXRzXG5cdCAqIGFuZCB0aGUgcmVnaXN0cnktcHJlZml4ZWQgYWxpYXNlcyBpbiB0eXBlcy50cyAvIHJlZ2lzdHJ5LnRzLlxuXHQgKi9cblx0d3JpdGVDb2xsZWN0aW9uc0ZpbGUgKGNvbGxlY3Rpb25zOiBDb2xsZWN0aW9uTWFuaWZlc3RFbnRyeVtdKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnY29sbGVjdGlvbnMuanNvbicpO1xuXG5cdFx0Y29uc3QganNvbjogQ29sbGVjdGlvbnNKc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdGNvbGxlY3Rpb25zLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxufVxuIl19