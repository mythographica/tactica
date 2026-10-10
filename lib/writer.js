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
     * Write definitions.json file. When the type graph is passed (the CLI
     * always passes it), each entry gains `fields` (the type's own fields in
     * declaration order, from TypeNode.properties) and `args` (the
     * constructor's parameters, from TypeNode.constructorParams) — the same
     * source of truth types.ts renders. A rest parameter is emitted with
     * `kind: 'rest'` and no `optional` (lethe definitions contract); `args`
     * is omitted only when constructorParams was never extracted.
     */
    writeDefinitionsFile(definitions, graph) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'definitions.json');
        // Convert Map to plain object
        const definitionsObj = {};
        for (const [key, value] of definitions) {
            definitionsObj[key] = value;
        }
        if (graph) {
            for (const [key, value] of definitions) {
                const node = graph.findType(key);
                if (!node) {
                    continue;
                }
                // enrich a copy — the analyzer's definitions map stays untouched
                const entry = { ...value };
                const fields = [];
                for (const propInfo of node.properties.values()) {
                    fields.push({
                        name: propInfo.name,
                        type: propInfo.type,
                        optional: propInfo.optional
                    });
                }
                entry.fields = fields;
                if (node.constructorParams !== undefined) {
                    const args = node.constructorParams.map((param) => {
                        // a rest parameter may always receive nothing:
                        // the contract gives it `kind` and no `optional`
                        const arg = param.kind === 'rest'
                            ? {
                                name: param.name,
                                type: param.type,
                                kind: 'rest'
                            }
                            : {
                                name: param.name,
                                type: param.type,
                                optional: param.optional
                            };
                        return arg;
                    });
                    entry.args = args;
                }
                definitionsObj[key] = entry;
            }
        }
        const json = this.relativize({
            version: '1.1',
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
            version: '1.1',
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
            version: '1.1',
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
     * Write control.json file (lethe contract, format 1.1): `callers` is the
     * creation graph instrumentation.json v2 carries, `points` the same
     * plugin-supplied instrumentation points. instrumentation.json keeps its
     * shape for mnemographica; control.json is the cross-language contract
     * rendering of the same data.
     */
    writeControlFile(points, callers) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'control.json');
        const json = {
            version: '1.1',
            generatedAt: new Date().toISOString(),
            callers,
            points,
        };
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
            version: '1.1',
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
            version: '1.1',
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
            version: '1.1',
            generatedAt: new Date().toISOString(),
            collections,
        });
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
}
exports.TypesWriter = TypesWriter;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoid3JpdGVyLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL3dyaXRlci50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLHVDQUF5QjtBQUN6QiwyQ0FBNkI7QUFPN0I7O0dBRUc7QUFDSCxNQUFhLFdBQVc7SUFJdkIsWUFBYSxTQUFTLEdBQUcsVUFBVSxFQUFFLFdBQW9CO1FBQ3hELElBQUksQ0FBQyxTQUFTLEdBQUcsU0FBUyxDQUFDO1FBQzNCLElBQUksQ0FBQyxXQUFXLEdBQUcsV0FBVyxLQUFLLFNBQVM7WUFDM0MsQ0FBQyxDQUFDLFNBQVM7WUFDWCxDQUFDLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxXQUFXLENBQUMsQ0FBQztJQUM5QixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLFVBQVUsQ0FBSyxPQUFVO1FBQ2hDLElBQUksSUFBSSxDQUFDLFdBQVcsS0FBSyxTQUFTLEVBQUUsQ0FBQztZQUNwQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFdBQVcsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO1FBQzNDLE1BQU0sSUFBSSxHQUFHLENBQUMsS0FBYyxFQUFXLEVBQUU7WUFDeEMsSUFBSSxPQUFPLEtBQUssS0FBSyxRQUFRLEVBQUUsQ0FBQztnQkFDL0IsSUFBSSxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztvQkFDL0IsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztnQkFDRCxNQUFNLFFBQVEsR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQztnQkFDNUMsTUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxD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U0FBUyxDQUFDLElBQUksRUFBRSxJQUFJLEVBQUUsQ0FBQyxDQUFDLEVBQUUsT0FBTyxDQUFDLENBQUM7UUFDbkUsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOzs7Ozs7T0FNRztJQUNILG9CQUFvQixDQUFFLFdBQXNDO1FBQzNELElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztRQUN2QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsa0JBQWtCLENBQUMsQ0FBQztRQUUvRCxNQUFNLElBQUksR0FBb0IsSUFBSSxDQUFDLFVBQVUsQ0FBQztZQUM3QyxPQUFPLEVBQU8sS0FBSztZQUNuQixXQUFXLEVBQUcsSUFBSSxJQUFJLEVBQUUsQ0FBQyxXQUFXLEVBQUU7WUFDdEMsV0FBVztTQUNYLENBQUMsQ0FBQztRQUVILEVBQUUsQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxDQUFDLENBQUMsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUNuRSxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0NBQ0Q7QUFsWUQsa0NBa1lDIiwic291cmNlc0NvbnRlbnQiOlsiJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyBmcyBmcm9tICdmcyc7XG5pbXBvcnQgKiBhcyBwYXRoIGZyb20gJ3BhdGgnO1xuaW1wb3J0IHtcblx0R2VuZXJhdGVkVHlwZXMsIERlZmluaXRpb25JbmZvLCBVc2FnZUluZm8sIEVEU0luZm8sIEZsb3dJbmZvLCBGbG93SnNvbiwgSGllcmFyY2h5Tm9kZSwgSGllcmFyY2h5SnNvbixcblx0SW5zdHJ1bWVudGF0aW9uUG9pbnQsIEluc3RydW1lbnRhdGlvbkpzb24sIE1vZHVsZUdyYXBoLCBNb2R1bGVzSnNvbiwgU2NvcGVBbmFseXNpcywgU2NvcGVzSnNvbiwgQ3JlYXRpb25HcmFwaCxcblx0Q29sbGVjdGlvbk1hbmlmZXN0RW50cnksIENvbGxlY3Rpb25zSnNvbiwgQ29udHJvbEpzb24sIFR5cGVHcmFwaCwgRGVmaW5pdGlvbkZpZWxkLCBEZWZpbml0aW9uQXJnXG59IGZyb20gJy4vdHlwZXMnO1xuXG4vKipcbiAqIFdyaXRlcyBnZW5lcmF0ZWQgdHlwZXMgdG8gZmlsZSBzeXN0ZW1cbiAqL1xuZXhwb3J0IGNsYXNzIFR5cGVzV3JpdGVyIHtcblx0cHJpdmF0ZSBvdXRwdXREaXI6IHN0cmluZztcblx0cHJpdmF0ZSBwcm9qZWN0Um9vdD86IHN0cmluZztcblxuXHRjb25zdHJ1Y3RvciAob3V0cHV0RGlyID0gJy50YWN0aWNhJywgcHJvamVjdFJvb3Q/OiBzdHJpbmcpIHtcblx0XHR0aGlzLm91dHB1dERpciA9IG91dHB1dERpcjtcblx0XHR0aGlzLnByb2plY3RSb290ID0gcHJvamVjdFJvb3QgPT09IHVuZGVmaW5lZFxuXHRcdFx0PyB1bmRlZmluZWRcblx0XHRcdDogcGF0aC5yZXNvbHZlKHByb2plY3RSb290KTtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXdyaXRlIGV2ZXJ5IHByb2plY3Qtcm9vdGVkIGFic29sdXRlIHBhdGggaW4gdGhlIHBheWxvYWQgdG8gYVxuXHQgKiBwcm9qZWN0LXJlbGF0aXZlIG9uZSAodmFsdWVzIEFORCBvYmplY3Qga2V5cyksIHNvIC50YWN0aWNhIG91dHB1dFxuXHQgKiBzdGF5cyBwb3J0YWJsZSBhY3Jvc3MgbWFjaGluZXMgYW5kIGNoZWNrb3V0cy4gUGF0aHMgb3V0c2lkZSB0aGVcblx0ICogcHJvamVjdCByb290IGtlZXAgdGhlaXIgYWJzb2x1dGUgZm9ybSDigJQgdGhleSBnZW51aW5lbHkgYXJlXG5cdCAqIG1hY2hpbmUtc3BlY2lmaWMuIENvbnN1bWVycyByZXNvbHZlIHJlbGF0aXZlIGVudHJpZXMgYWdhaW5zdCB0aGVcblx0ICogZGlyZWN0b3J5IHRoYXQgaG9sZHMgLnRhY3RpY2EuXG5cdCAqL1xuXHRwcml2YXRlIHJlbGF0aXZpemU8VD4gKHBheWxvYWQ6IFQpOiBUIHtcblx0XHRpZiAodGhpcy5wcm9qZWN0Um9vdCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRyZXR1cm4gcGF5bG9hZDtcblx0XHR9XG5cdFx0Y29uc3QgcHJlZml4ID0gdGhpcy5wcm9qZWN0Um9vdCArIHBhdGguc2VwO1xuXHRcdGNvbnN0IHdhbGsgPSAoaW5wdXQ6IHVua25vd24pOiB1bmtub3duID0+IHtcblx0XHRcdGlmICh0eXBlb2YgaW5wdXQgPT09ICdzdHJpbmcnKSB7XG5cdFx0XHRcdGlmICghaW5wdXQuc3RhcnRzV2l0aChwcmVmaXgpKSB7XG5cdFx0XHRcdFx0cmV0dXJuIGlucHV0O1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IHJlbGF0aXZlID0gaW5wdXQuc2xpY2UocHJlZml4Lmxlbmd0aCk7XG5cdFx0XHRcdGNvbnN0IHdhbGtlZCA9IHJlbGF0aXZlLnNwbGl0KHBhdGguc2VwKS5qb2luKCcvJyk7XG5cdFx0XHRcdHJldHVybiB3YWxrZWQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAoQXJyYXkuaXNBcnJheShpbnB1dCkpIHtcblx0XHRcdFx0Y29uc3Qgd2Fsa2VkID0gaW5wdXQubWFwKHdhbGspO1xuXHRcdFx0XHRyZXR1cm4gd2Fsa2VkO1xuXHRcdFx0fVxuXHRcdFx0aWYgKGlucHV0ICE9PSBudWxsICYmIHR5cGVvZiBpbnB1dCA9PT0gJ29iamVjdCcpIHtcblx0XHRcdFx0Y29uc3Qgd2Fsa2VkOiBSZWNvcmQ8c3RyaW5nLCB1bmtub3duPiA9IHt9O1xuXHRcdFx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIE9iamVjdC5lbnRyaWVzKGlucHV0KSkge1xuXHRcdFx0XHRcdGNvbnN0IHdhbGtlZEtleSA9IHdhbGsoa2V5KSBhcyBzdHJpbmc7XG5cdFx0XHRcdFx0d2Fsa2VkWyB3YWxrZWRLZXkgXSA9IHdhbGsodmFsdWUpO1xuXHRcdFx0XHR9XG5cdFx0XHRcdHJldHVybiB3YWxrZWQ7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gaW5wdXQ7XG5cdFx0fTtcblx0XHRjb25zdCByZXN1bHQgPSB3YWxrKHBheWxvYWQpO1xuXHRcdHJldHVybiByZXN1bHQgYXMgVDtcblx0fVxuXG5cdC8qKlxuXHQgKiBMZWdhY3kgd3JpdGUgbWV0aG9kIC0gZGVsZWdhdGVzIHRvIHdyaXRlVHlwZXNGaWxlXG5cdCAqL1xuXHR3cml0ZSAoZ2VuZXJhdGVkOiBHZW5lcmF0ZWRUeXBlcyk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIHRoaXMud3JpdGVUeXBlc0ZpbGUoZ2VuZXJhdGVkKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB0eXBlcy50cyBmaWxlIChleHBvcnRhYmxlIHR5cGUgYWxpYXNlcyAtIGRlZmF1bHQgbW9kZSlcblx0ICovXG5cdHdyaXRlVHlwZXNGaWxlIChnZW5lcmF0ZWQ6IEdlbmVyYXRlZFR5cGVzKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAndHlwZXMudHMnKTtcblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBnZW5lcmF0ZWQuY29udGVudCwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGdsb2JhbCBhdWdtZW50YXRpb24gZmlsZSAoaW5kZXguZC50cyAtIG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZSlcblx0ICovXG5cdHdyaXRlR2xvYmFsQXVnbWVudGF0aW9uIChnZW5lcmF0ZWQ6IEdlbmVyYXRlZFR5cGVzKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnaW5kZXguZC50cycpO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIGdlbmVyYXRlZC5jb250ZW50LCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgdG8gYSBjdXN0b20gZmlsZW5hbWVcblx0ICovXG5cdHdyaXRlVG8gKGZpbGVuYW1lOiBzdHJpbmcsIGNvbnRlbnQ6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgZmlsZW5hbWUpO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIGNvbnRlbnQsICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbnN1cmUgb3V0cHV0IGRpcmVjdG9yeSBleGlzdHNcblx0ICovXG5cdHByaXZhdGUgZW5zdXJlRGlyZWN0b3J5ICgpOiB2b2lkIHtcblx0XHRpZiAoIWZzLmV4aXN0c1N5bmModGhpcy5vdXRwdXREaXIpKSB7XG5cdFx0XHRmcy5ta2RpclN5bmModGhpcy5vdXRwdXREaXIsIHsgcmVjdXJzaXZlIDogdHJ1ZSB9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ2xlYW4gdGhlIG91dHB1dCBkaXJlY3Rvcnlcblx0ICovXG5cdGNsZWFuICgpOiB2b2lkIHtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyh0aGlzLm91dHB1dERpcikpIHtcblx0XHRcdGNvbnN0IGZpbGVzID0gZnMucmVhZGRpclN5bmModGhpcy5vdXRwdXREaXIpO1xuXHRcdFx0Zm9yIChjb25zdCBmaWxlIG9mIGZpbGVzKSB7XG5cdFx0XHRcdGZzLnVubGlua1N5bmMocGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCBmaWxlKSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBvdXRwdXQgZGlyZWN0b3J5XG5cdCAqL1xuXHRnZXRPdXRwdXREaXIgKCk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIHRoaXMub3V0cHV0RGlyO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGRlZmluaXRpb25zLmpzb24gZmlsZS4gV2hlbiB0aGUgdHlwZSBncmFwaCBpcyBwYXNzZWQgKHRoZSBDTElcblx0ICogYWx3YXlzIHBhc3NlcyBpdCksIGVhY2ggZW50cnkgZ2FpbnMgYGZpZWxkc2AgKHRoZSB0eXBlJ3Mgb3duIGZpZWxkcyBpblxuXHQgKiBkZWNsYXJhdGlvbiBvcmRlciwgZnJvbSBUeXBlTm9kZS5wcm9wZXJ0aWVzKSBhbmQgYGFyZ3NgICh0aGVcblx0ICogY29uc3RydWN0b3IncyBwYXJhbWV0ZXJzLCBmcm9tIFR5cGVOb2RlLmNvbnN0cnVjdG9yUGFyYW1zKSDigJQgdGhlIHNhbWVcblx0ICogc291cmNlIG9mIHRydXRoIHR5cGVzLnRzIHJlbmRlcnMuIEEgcmVzdCBwYXJhbWV0ZXIgaXMgZW1pdHRlZCB3aXRoXG5cdCAqIGBraW5kOiAncmVzdCdgIGFuZCBubyBgb3B0aW9uYWxgIChsZXRoZSBkZWZpbml0aW9ucyBjb250cmFjdCk7IGBhcmdzYFxuXHQgKiBpcyBvbWl0dGVkIG9ubHkgd2hlbiBjb25zdHJ1Y3RvclBhcmFtcyB3YXMgbmV2ZXIgZXh0cmFjdGVkLlxuXHQgKi9cblx0d3JpdGVEZWZpbml0aW9uc0ZpbGUgKGRlZmluaXRpb25zOiBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4sIGdyYXBoPzogVHlwZUdyYXBoKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnZGVmaW5pdGlvbnMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZGVmaW5pdGlvbnNPYmo6IFJlY29yZDxzdHJpbmcsIERlZmluaXRpb25JbmZvPiA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRcdGRlZmluaXRpb25zT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblxuXHRcdGlmIChncmFwaCkge1xuXHRcdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdFx0XHRjb25zdCBub2RlID0gZ3JhcGguZmluZFR5cGUoa2V5KTtcblx0XHRcdFx0aWYgKCFub2RlKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gZW5yaWNoIGEgY29weSDigJQgdGhlIGFuYWx5emVyJ3MgZGVmaW5pdGlvbnMgbWFwIHN0YXlzIHVudG91Y2hlZFxuXHRcdFx0XHRjb25zdCBlbnRyeTogRGVmaW5pdGlvbkluZm8gPSB7IC4uLnZhbHVlIH07XG5cdFx0XHRcdGNvbnN0IGZpZWxkczogRGVmaW5pdGlvbkZpZWxkW10gPSBbXTtcblx0XHRcdFx0Zm9yIChjb25zdCBwcm9wSW5mbyBvZiBub2RlLnByb3BlcnRpZXMudmFsdWVzKCkpIHtcblx0XHRcdFx0XHRmaWVsZHMucHVzaCh7XG5cdFx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BJbmZvLm5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlICAgICA6IHByb3BJbmZvLnR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IHByb3BJbmZvLm9wdGlvbmFsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0ZW50cnkuZmllbGRzID0gZmllbGRzO1xuXHRcdFx0XHRpZiAobm9kZS5jb25zdHJ1Y3RvclBhcmFtcyAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0Y29uc3QgYXJnczogRGVmaW5pdGlvbkFyZ1tdID0gbm9kZS5jb25zdHJ1Y3RvclBhcmFtcy5tYXAoKHBhcmFtKSA9PiB7XG5cdFx0XHRcdFx0XHQvLyBhIHJlc3QgcGFyYW1ldGVyIG1heSBhbHdheXMgcmVjZWl2ZSBub3RoaW5nOlxuXHRcdFx0XHRcdFx0Ly8gdGhlIGNvbnRyYWN0IGdpdmVzIGl0IGBraW5kYCBhbmQgbm8gYG9wdGlvbmFsYFxuXHRcdFx0XHRcdFx0Y29uc3QgYXJnOiBEZWZpbml0aW9uQXJnID0gcGFyYW0ua2luZCA9PT0gJ3Jlc3QnXG5cdFx0XHRcdFx0XHRcdD8ge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUgOiBwYXJhbS5uYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUgOiBwYXJhbS50eXBlLFxuXHRcdFx0XHRcdFx0XHRcdGtpbmQgOiAncmVzdCdcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHQ6IHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtLm5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiBwYXJhbS50eXBlLFxuXHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogcGFyYW0ub3B0aW9uYWxcblx0XHRcdFx0XHRcdFx0fTtcblx0XHRcdFx0XHRcdHJldHVybiBhcmc7XG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0ZW50cnkuYXJncyA9IGFyZ3M7XG5cdFx0XHRcdH1cblx0XHRcdFx0ZGVmaW5pdGlvbnNPYmpbIGtleSBdID0gZW50cnk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjEnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRkZWZpbml0aW9ucyA6IGRlZmluaXRpb25zT2JqLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB1c2FnZXMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZVVzYWdlc0ZpbGUgKHVzYWdlczogTWFwPHN0cmluZywgVXNhZ2VJbmZvW10+KTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAndXNhZ2VzLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwIHRvIHBsYWluIG9iamVjdFxuXHRcdGNvbnN0IHVzYWdlc09iajogUmVjb3JkPHN0cmluZywgVXNhZ2VJbmZvW10+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiB1c2FnZXMpIHtcblx0XHRcdHVzYWdlc09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMScsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdHVzYWdlcyAgICAgIDogdXNhZ2VzT2JqLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBlZHMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZUVEU0ZpbGUgKGVkczogTWFwPHN0cmluZywgRURTSW5mb1tdPik6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2Vkcy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBlZHNPYmo6IFJlY29yZDxzdHJpbmcsIEVEU0luZm9bXT4gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGVkcykge1xuXHRcdFx0ZWRzT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGpzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4xJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0ZWRzICAgICAgICAgOiBlZHNPYmosXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGluc3RydW1lbnRhdGlvbi5qc29uIGZpbGUgKHYyOiBhZGRzIHRoZSBjcmVhdGlvbkdyYXBoIGtleSB3aGVuXG5cdCAqIHRoZSBjYWxsZXIgcGFzc2VzIGNyZWF0aW9uLWdyYXBoIGRhdGEg4oCUIHRoZSBDTEkgYWx3YXlzIGRvZXMpXG5cdCAqL1xuXHR3cml0ZUluc3RydW1lbnRhdGlvbkZpbGUgKHBvaW50czogSW5zdHJ1bWVudGF0aW9uUG9pbnRbXSwgY3JlYXRpb25HcmFwaD86IENyZWF0aW9uR3JhcGgpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdpbnN0cnVtZW50YXRpb24uanNvbicpO1xuXG5cdFx0Y29uc3QganNvbjogSW5zdHJ1bWVudGF0aW9uSnNvbiA9IHtcblx0XHRcdHZlcnNpb24gICAgIDogMixcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0cG9pbnRzLFxuXHRcdH07XG5cdFx0aWYgKGNyZWF0aW9uR3JhcGgpIHtcblx0XHRcdGpzb24uY3JlYXRpb25HcmFwaCA9IGNyZWF0aW9uR3JhcGg7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVsYXRpdml6ZWQgPSB0aGlzLnJlbGF0aXZpemUoanNvbik7XG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkocmVsYXRpdml6ZWQsIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgY29udHJvbC5qc29uIGZpbGUgKGxldGhlIGNvbnRyYWN0LCBmb3JtYXQgMS4xKTogYGNhbGxlcnNgIGlzIHRoZVxuXHQgKiBjcmVhdGlvbiBncmFwaCBpbnN0cnVtZW50YXRpb24uanNvbiB2MiBjYXJyaWVzLCBgcG9pbnRzYCB0aGUgc2FtZVxuXHQgKiBwbHVnaW4tc3VwcGxpZWQgaW5zdHJ1bWVudGF0aW9uIHBvaW50cy4gaW5zdHJ1bWVudGF0aW9uLmpzb24ga2VlcHMgaXRzXG5cdCAqIHNoYXBlIGZvciBtbmVtb2dyYXBoaWNhOyBjb250cm9sLmpzb24gaXMgdGhlIGNyb3NzLWxhbmd1YWdlIGNvbnRyYWN0XG5cdCAqIHJlbmRlcmluZyBvZiB0aGUgc2FtZSBkYXRhLlxuXHQgKi9cblx0d3JpdGVDb250cm9sRmlsZSAocG9pbnRzOiBJbnN0cnVtZW50YXRpb25Qb2ludFtdLCBjYWxsZXJzOiBDcmVhdGlvbkdyYXBoKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnY29udHJvbC5qc29uJyk7XG5cblx0XHRjb25zdCBqc29uOiBDb250cm9sSnNvbiA9IHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMScsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdGNhbGxlcnMsXG5cdFx0XHRwb2ludHMsXG5cdFx0fTtcblxuXHRcdGNvbnN0IHJlbGF0aXZpemVkID0gdGhpcy5yZWxhdGl2aXplKGpzb24pO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KHJlbGF0aXZpemVkLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGZsb3cuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZUZsb3dGaWxlIChmbG93OiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPik6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2Zsb3cuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZmxvd09iajogUmVjb3JkPHN0cmluZywgRmxvd0luZm9bXT4gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGZsb3cpIHtcblx0XHRcdGZsb3dPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbjogRmxvd0pzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4xJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0ZmxvdyAgICAgICAgOiBmbG93T2JqLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBtb2R1bGVzLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVNb2R1bGVzRmlsZSAoZ3JhcGg6IE1vZHVsZUdyYXBoKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnbW9kdWxlcy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBtb2R1bGVzT2JqOiBNb2R1bGVzSnNvblsgJ21vZHVsZXMnIF0gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGdyYXBoLm1vZHVsZXMpIHtcblx0XHRcdG1vZHVsZXNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbjogTW9kdWxlc0pzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0bW9kdWxlcyAgICAgOiBtb2R1bGVzT2JqLFxuXHRcdFx0ZWRnZXMgICAgICAgOiBncmFwaC5lZGdlcyxcblx0XHRcdGN5Y2xlcyAgICAgIDogZ3JhcGguY3ljbGVzLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBzY29wZXMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZVNjb3Blc0ZpbGUgKGFuYWx5c2lzOiBTY29wZUFuYWx5c2lzKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnc2NvcGVzLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwcyB0byBwbGFpbiBzaGFwZXNcblx0XHRjb25zdCBzY29wZXNPYmo6IFNjb3Blc0pzb25bICdzY29wZXMnIF0gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGFuYWx5c2lzLnNjb3Blcykge1xuXHRcdFx0c2NvcGVzT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblx0XHRjb25zdCB2YXJpYWJsZXMgPSBBcnJheS5mcm9tKGFuYWx5c2lzLnZhcmlhYmxlcy52YWx1ZXMoKSk7XG5cblx0XHRjb25zdCBqc29uOiBTY29wZXNKc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdHNjb3BlcyAgICAgIDogc2NvcGVzT2JqLFxuXHRcdFx0dmFyaWFibGVzLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBoaWVyYXJjaHkuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZUhpZXJhcmNoeUZpbGUgKHJvb3RzOiBIaWVyYXJjaHlOb2RlW10pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdoaWVyYXJjaHkuanNvbicpO1xuXG5cdFx0Y29uc3QganNvbjogSGllcmFyY2h5SnNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjEnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRyb290cyxcblx0XHR9KTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgdGhlIGNvbGxlY3Rpb24gbWFuaWZlc3Q6IG9uZSBlbnRyeSBwZXIgY29sbGVjdGlvbiAoZGVmYXVsdFxuXHQgKiBmaXJzdCB3aGVuIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBleGlzdCksIGlkcyArIGRpc3BsYXkgbmFtZXMgK1xuXHQgKiBPcHRpb24tQiByZWdpc3RyeSBpbnRlcmZhY2VzICsgY2FsbCBzaXRlcy4gVGhlIGlk4oaUaW50ZXJmYWNlIG1hcHBpbmdcblx0ICogaXMgdGhlIGpvaW4ga2V5IGJldHdlZW4gdGhlIGBjb2xsZWN0aW9uSWQ6OmAtcHJlZml4ZWQgZ3JhcGggb3V0cHV0c1xuXHQgKiBhbmQgdGhlIHJlZ2lzdHJ5LXByZWZpeGVkIGFsaWFzZXMgaW4gdHlwZXMudHMgLyByZWdpc3RyeS50cy5cblx0ICovXG5cdHdyaXRlQ29sbGVjdGlvbnNGaWxlIChjb2xsZWN0aW9uczogQ29sbGVjdGlvbk1hbmlmZXN0RW50cnlbXSk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2NvbGxlY3Rpb25zLmpzb24nKTtcblxuXHRcdGNvbnN0IGpzb246IENvbGxlY3Rpb25zSnNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjEnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRjb2xsZWN0aW9ucyxcblx0XHR9KTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cbn1cbiJdfQ==