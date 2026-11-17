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
 * A file's content without its top-level `generatedAt` stamp — the only
 * part of a run's output that changes when the project does not
 */
const withoutStamp = function (content) {
    const stripped = content.replace(/^ {2}"generatedAt": "[^"]*",?$/m, '');
    return stripped;
};
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
     * Open a run: the write methods hold their files until commit()
     */
    begin() {
        this.pending = [];
    }
    /**
     * Close the run. When every held file exists on disk with the same
     * content except its generatedAt stamp, nothing is written — no new
     * stamps, no file events for watchers. Otherwise every held file is
     * written: the stamps stay one run's set (consumers compare stamps
     * across files, e.g. an eds.json older than definitions.json reads
     * as stale). Returns whether anything was written.
     */
    commit() {
        const files = this.pending || [];
        this.pending = undefined;
        const unchanged = files.every(file => this.matchesDisk(file));
        if (!unchanged) {
            for (const file of files) {
                fs.writeFileSync(file.filePath, file.content, 'utf-8');
            }
        }
        const written = !unchanged;
        return written;
    }
    matchesDisk(file) {
        if (!fs.existsSync(file.filePath)) {
            return false;
        }
        const onDisk = fs.readFileSync(file.filePath, 'utf-8');
        const same = withoutStamp(onDisk) === withoutStamp(file.content);
        return same;
    }
    /**
     * Write a file now, or hold it for commit() while a run is open
     */
    emit(filePath, content) {
        if (this.pending) {
            this.pending.push({ filePath, content });
            return;
        }
        fs.writeFileSync(filePath, content, 'utf-8');
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
        this.emit(filePath, generated.content);
        return filePath;
    }
    /**
     * Write to a custom filename
     */
    writeTo(filename, content) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, filename);
        this.emit(filePath, content);
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
            version: '1.2',
            generatedAt: new Date().toISOString(),
            definitions: definitionsObj,
        });
        this.emit(filePath, JSON.stringify(json, null, 2));
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
            version: '1.2',
            generatedAt: new Date().toISOString(),
            usages: usagesObj,
        });
        this.emit(filePath, JSON.stringify(json, null, 2));
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
            version: '1.2',
            generatedAt: new Date().toISOString(),
            eds: edsObj,
        });
        this.emit(filePath, JSON.stringify(json, null, 2));
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
        this.emit(filePath, JSON.stringify(relativized, null, 2));
        return filePath;
    }
    /**
     * Write control.json file (lethe contract, format 1.2): `callers` is the
     * creation graph instrumentation.json v2 carries, `points` the same
     * plugin-supplied instrumentation points. instrumentation.json keeps its
     * shape for mnemographica; control.json is the cross-language contract
     * rendering of the same data.
     */
    writeControlFile(points, callers) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'control.json');
        const json = {
            version: '1.2',
            generatedAt: new Date().toISOString(),
            callers,
            points,
        };
        const relativized = this.relativize(json);
        this.emit(filePath, JSON.stringify(relativized, null, 2));
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
            version: '1.2',
            generatedAt: new Date().toISOString(),
            flow: flowObj,
        });
        this.emit(filePath, JSON.stringify(json, null, 2));
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
        this.emit(filePath, JSON.stringify(json, null, 2));
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
        this.emit(filePath, JSON.stringify(json, null, 2));
        return filePath;
    }
    /**
     * Write hierarchy.json file
     */
    writeHierarchyFile(roots) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'hierarchy.json');
        const json = this.relativize({
            version: '1.2',
            generatedAt: new Date().toISOString(),
            roots,
        });
        this.emit(filePath, JSON.stringify(json, null, 2));
        return filePath;
    }
    /**
     * Write the collection manifest: one entry per collection (default
     * first when default-collection types exist), ids + display names +
     * call sites + language. The `collectionId::` prefix on graph-output
     * fullPaths joins to the entry `id`. Format 1.2: the registry
     * interface is not part of the manifest — the registry-prefixed
     * aliases in types.ts / registry.ts come from the in-memory
     * TypeNode.registryInterfaceName instead.
     */
    writeCollectionsFile(collections) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'collections.json');
        const json = this.relativize({
            version: '1.2',
            generatedAt: new Date().toISOString(),
            collections,
        });
        this.emit(filePath, JSON.stringify(json, null, 2));
        return filePath;
    }
}
exports.TypesWriter = TypesWriter;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoid3JpdGVyLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL3dyaXRlci50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLHVDQUF5QjtBQUN6QiwyQ0FBNkI7QUFPN0I7OztHQUdHO0FBQ0gsTUFBTSxZQUFZLEdBQUcsVUFBVSxPQUFlO0lBQzdDLE1BQU0sUUFBUSxHQUFHLE9BQU8sQ0FBQyxPQUFPLENBQUMsaUNBQWlDLEVBQUUsRUFBRSxDQUFDLENBQUM7SUFDeEUsT0FBTyxRQUFRLENBQUM7QUFDakIsQ0FBQyxDQUFDO0FBT0Y7O0dBRUc7QUFDSCxNQUFhLFdBQVc7SUFRdkIsWUFBYSxTQUFTLEdBQUcsVUFBVSxFQUFFLFdBQW9CO1FBQ3hELElBQUksQ0FBQyxTQUFTLEdBQUcsU0FBUyxDQUFDO1FBQzNCLElBQUksQ0FBQyxXQUFXLEdBQUcsV0FBVyxLQUFLLFNBQVM7WUFDM0MsQ0FBQyxDQUFDLFNBQVM7WUFDWCxDQUFDLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxXQUFXLENBQUMsQ0FBQztJQUM5QixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLFVBQVUsQ0FBSyxPQUFVO1FBQ2hDLElBQUksSUFBSSxDQUFDLFdBQVcsS0FBSyxTQUFTLEVBQUUsQ0FBQztZQUNwQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFdBQVcsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO1FBQzNDLE1BQU0sSUFBSSxHQUFHLENBQUMsS0FBYyxFQUFXLEVBQUU7WUFDeEMsSUFBSSxPQUFPLEtBQUssS0FBSyxRQUFRLEVBQUUsQ0FBQztnQkFDL0IsSUFBSSxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztvQkFDL0IsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztnQkFDRCxN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LENBQUMsQ0FBQyxDQUFDLENBQUM7UUFDbkQsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOzs7Ozs7OztPQVFHO0lBQ0gsb0JBQW9CLENBQUUsV0FBc0M7UUFDM0QsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1FBQ3ZCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxrQkFBa0IsQ0FBQyxDQUFDO1FBRS9ELE1BQU0sSUFBSSxHQUFvQixJQUFJLENBQUMsVUFBVSxDQUFDO1lBQzdDLE9BQU8sRUFBTyxLQUFLO1lBQ25CLFdBQVcsRUFBRyxJQUFJLElBQUksRUFBRSxDQUFDLFdBQVcsRUFBRTtZQUN0QyxXQUFXO1NBQ1gsQ0FBQyxDQUFDO1FBRUgsSUFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxDQUFDLENBQUM7UUFDbkQsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztDQUNEO0FBOWFELGtDQThhQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgZnMgZnJvbSAnZnMnO1xuaW1wb3J0ICogYXMgcGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCB7XG5cdEdlbmVyYXRlZFR5cGVzLCBEZWZpbml0aW9uSW5mbywgVXNhZ2VJbmZvLCBFRFNJbmZvLCBGbG93SW5mbywgRmxvd0pzb24sIEhpZXJhcmNoeU5vZGUsIEhpZXJhcmNoeUpzb24sXG5cdEluc3RydW1lbnRhdGlvblBvaW50LCBJbnN0cnVtZW50YXRpb25Kc29uLCBNb2R1bGVHcmFwaCwgTW9kdWxlc0pzb24sIFNjb3BlQW5hbHlzaXMsIFNjb3Blc0pzb24sIENyZWF0aW9uR3JhcGgsXG5cdENvbGxlY3Rpb25NYW5pZmVzdEVudHJ5LCBDb2xsZWN0aW9uc0pzb24sIENvbnRyb2xKc29uLCBUeXBlR3JhcGgsIERlZmluaXRpb25GaWVsZCwgRGVmaW5pdGlvbkFyZ1xufSBmcm9tICcuL3R5cGVzJztcblxuLyoqXG4gKiBBIGZpbGUncyBjb250ZW50IHdpdGhvdXQgaXRzIHRvcC1sZXZlbCBgZ2VuZXJhdGVkQXRgIHN0YW1wIOKAlCB0aGUgb25seVxuICogcGFydCBvZiBhIHJ1bidzIG91dHB1dCB0aGF0IGNoYW5nZXMgd2hlbiB0aGUgcHJvamVjdCBkb2VzIG5vdFxuICovXG5jb25zdCB3aXRob3V0U3RhbXAgPSBmdW5jdGlvbiAoY29udGVudDogc3RyaW5nKTogc3RyaW5nIHtcblx0Y29uc3Qgc3RyaXBwZWQgPSBjb250ZW50LnJlcGxhY2UoL14gezJ9XCJnZW5lcmF0ZWRBdFwiOiBcIlteXCJdKlwiLD8kL20sICcnKTtcblx0cmV0dXJuIHN0cmlwcGVkO1xufTtcblxuaW50ZXJmYWNlIFBlbmRpbmdGaWxlIHtcblx0ZmlsZVBhdGg6IHN0cmluZztcblx0Y29udGVudDogc3RyaW5nO1xufVxuXG4vKipcbiAqIFdyaXRlcyBnZW5lcmF0ZWQgdHlwZXMgdG8gZmlsZSBzeXN0ZW1cbiAqL1xuZXhwb3J0IGNsYXNzIFR5cGVzV3JpdGVyIHtcblx0cHJpdmF0ZSBvdXRwdXREaXI6IHN0cmluZztcblx0cHJpdmF0ZSBwcm9qZWN0Um9vdD86IHN0cmluZztcblx0Ly8gVGhlIGZpbGVzIG9mIGFuIG9wZW4gcnVuIChiZWdpbigpIOKApiBjb21taXQoKSk6IGhlbGQsIHRoZW4gd3JpdHRlblxuXHQvLyBhbGwgdG9nZXRoZXIg4oCUIG9yIG5vdCBhdCBhbGwgd2hlbiB0aGV5IG1hdGNoIHRoZSBmaWxlcyBvbiBkaXNrXG5cdC8vIGV4Y2VwdCBmb3IgdGhlIGdlbmVyYXRlZEF0IHN0YW1wc1xuXHRwcml2YXRlIHBlbmRpbmc6IFBlbmRpbmdGaWxlW10gfCB1bmRlZmluZWQ7XG5cblx0Y29uc3RydWN0b3IgKG91dHB1dERpciA9ICcudGFjdGljYScsIHByb2plY3RSb290Pzogc3RyaW5nKSB7XG5cdFx0dGhpcy5vdXRwdXREaXIgPSBvdXRwdXREaXI7XG5cdFx0dGhpcy5wcm9qZWN0Um9vdCA9IHByb2plY3RSb290ID09PSB1bmRlZmluZWRcblx0XHRcdD8gdW5kZWZpbmVkXG5cdFx0XHQ6IHBhdGgucmVzb2x2ZShwcm9qZWN0Um9vdCk7XG5cdH1cblxuXHQvKipcblx0ICogUmV3cml0ZSBldmVyeSBwcm9qZWN0LXJvb3RlZCBhYnNvbHV0ZSBwYXRoIGluIHRoZSBwYXlsb2FkIHRvIGFcblx0ICogcHJvamVjdC1yZWxhdGl2ZSBvbmUgKHZhbHVlcyBBTkQgb2JqZWN0IGtleXMpLCBzbyAudGFjdGljYSBvdXRwdXRcblx0ICogc3RheXMgcG9ydGFibGUgYWNyb3NzIG1hY2hpbmVzIGFuZCBjaGVja291dHMuIFBhdGhzIG91dHNpZGUgdGhlXG5cdCAqIHByb2plY3Qgcm9vdCBrZWVwIHRoZWlyIGFic29sdXRlIGZvcm0g4oCUIHRoZXkgZ2VudWluZWx5IGFyZVxuXHQgKiBtYWNoaW5lLXNwZWNpZmljLiBDb25zdW1lcnMgcmVzb2x2ZSByZWxhdGl2ZSBlbnRyaWVzIGFnYWluc3QgdGhlXG5cdCAqIGRpcmVjdG9yeSB0aGF0IGhvbGRzIC50YWN0aWNhLlxuXHQgKi9cblx0cHJpdmF0ZSByZWxhdGl2aXplPFQ+IChwYXlsb2FkOiBUKTogVCB7XG5cdFx0aWYgKHRoaXMucHJvamVjdFJvb3QgPT09IHVuZGVmaW5lZCkge1xuXHRcdFx0cmV0dXJuIHBheWxvYWQ7XG5cdFx0fVxuXHRcdGNvbnN0IHByZWZpeCA9IHRoaXMucHJvamVjdFJvb3QgKyBwYXRoLnNlcDtcblx0XHRjb25zdCB3YWxrID0gKGlucHV0OiB1bmtub3duKTogdW5rbm93biA9PiB7XG5cdFx0XHRpZiAodHlwZW9mIGlucHV0ID09PSAnc3RyaW5nJykge1xuXHRcdFx0XHRpZiAoIWlucHV0LnN0YXJ0c1dpdGgocHJlZml4KSkge1xuXHRcdFx0XHRcdHJldHVybiBpbnB1dDtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCByZWxhdGl2ZSA9IGlucHV0LnNsaWNlKHByZWZpeC5sZW5ndGgpO1xuXHRcdFx0XHRjb25zdCB3YWxrZWQgPSByZWxhdGl2ZS5zcGxpdChwYXRoLnNlcCkuam9pbignLycpO1xuXHRcdFx0XHRyZXR1cm4gd2Fsa2VkO1xuXHRcdFx0fVxuXHRcdFx0aWYgKEFycmF5LmlzQXJyYXkoaW5wdXQpKSB7XG5cdFx0XHRcdGNvbnN0IHdhbGtlZCA9IGlucHV0Lm1hcCh3YWxrKTtcblx0XHRcdFx0cmV0dXJuIHdhbGtlZDtcblx0XHRcdH1cblx0XHRcdGlmIChpbnB1dCAhPT0gbnVsbCAmJiB0eXBlb2YgaW5wdXQgPT09ICdvYmplY3QnKSB7XG5cdFx0XHRcdGNvbnN0IHdhbGtlZDogUmVjb3JkPHN0cmluZywgdW5rbm93bj4gPSB7fTtcblx0XHRcdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBPYmplY3QuZW50cmllcyhpbnB1dCkpIHtcblx0XHRcdFx0XHRjb25zdCB3YWxrZWRLZXkgPSB3YWxrKGtleSkgYXMgc3RyaW5nO1xuXHRcdFx0XHRcdHdhbGtlZFsgd2Fsa2VkS2V5IF0gPSB3YWxrKHZhbHVlKTtcblx0XHRcdFx0fVxuXHRcdFx0XHRyZXR1cm4gd2Fsa2VkO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIGlucHV0O1xuXHRcdH07XG5cdFx0Y29uc3QgcmVzdWx0ID0gd2FsayhwYXlsb2FkKTtcblx0XHRyZXR1cm4gcmVzdWx0IGFzIFQ7XG5cdH1cblxuXHQvKipcblx0ICogT3BlbiBhIHJ1bjogdGhlIHdyaXRlIG1ldGhvZHMgaG9sZCB0aGVpciBmaWxlcyB1bnRpbCBjb21taXQoKVxuXHQgKi9cblx0YmVnaW4gKCk6IHZvaWQge1xuXHRcdHRoaXMucGVuZGluZyA9IFtdO1xuXHR9XG5cblx0LyoqXG5cdCAqIENsb3NlIHRoZSBydW4uIFdoZW4gZXZlcnkgaGVsZCBmaWxlIGV4aXN0cyBvbiBkaXNrIHdpdGggdGhlIHNhbWVcblx0ICogY29udGVudCBleGNlcHQgaXRzIGdlbmVyYXRlZEF0IHN0YW1wLCBub3RoaW5nIGlzIHdyaXR0ZW4g4oCUIG5vIG5ld1xuXHQgKiBzdGFtcHMsIG5vIGZpbGUgZXZlbnRzIGZvciB3YXRjaGVycy4gT3RoZXJ3aXNlIGV2ZXJ5IGhlbGQgZmlsZSBpc1xuXHQgKiB3cml0dGVuOiB0aGUgc3RhbXBzIHN0YXkgb25lIHJ1bidzIHNldCAoY29uc3VtZXJzIGNvbXBhcmUgc3RhbXBzXG5cdCAqIGFjcm9zcyBmaWxlcywgZS5nLiBhbiBlZHMuanNvbiBvbGRlciB0aGFuIGRlZmluaXRpb25zLmpzb24gcmVhZHNcblx0ICogYXMgc3RhbGUpLiBSZXR1cm5zIHdoZXRoZXIgYW55dGhpbmcgd2FzIHdyaXR0ZW4uXG5cdCAqL1xuXHRjb21taXQgKCk6IGJvb2xlYW4ge1xuXHRcdGNvbnN0IGZpbGVzID0gdGhpcy5wZW5kaW5nIHx8IFtdO1xuXHRcdHRoaXMucGVuZGluZyA9IHVuZGVmaW5lZDtcblx0XHRjb25zdCB1bmNoYW5nZWQgPSBmaWxlcy5ldmVyeShmaWxlID0+IHRoaXMubWF0Y2hlc0Rpc2soZmlsZSkpO1xuXHRcdGlmICghdW5jaGFuZ2VkKSB7XG5cdFx0XHRmb3IgKGNvbnN0IGZpbGUgb2YgZmlsZXMpIHtcblx0XHRcdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlLmZpbGVQYXRoLCBmaWxlLmNvbnRlbnQsICd1dGYtOCcpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRjb25zdCB3cml0dGVuID0gIXVuY2hhbmdlZDtcblx0XHRyZXR1cm4gd3JpdHRlbjtcblx0fVxuXG5cdHByaXZhdGUgbWF0Y2hlc0Rpc2sgKGZpbGU6IFBlbmRpbmdGaWxlKTogYm9vbGVhbiB7XG5cdFx0aWYgKCFmcy5leGlzdHNTeW5jKGZpbGUuZmlsZVBhdGgpKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXHRcdGNvbnN0IG9uRGlzayA9IGZzLnJlYWRGaWxlU3luYyhmaWxlLmZpbGVQYXRoLCAndXRmLTgnKTtcblx0XHRjb25zdCBzYW1lID0gd2l0aG91dFN0YW1wKG9uRGlzaykgPT09IHdpdGhvdXRTdGFtcChmaWxlLmNvbnRlbnQpO1xuXHRcdHJldHVybiBzYW1lO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGEgZmlsZSBub3csIG9yIGhvbGQgaXQgZm9yIGNvbW1pdCgpIHdoaWxlIGEgcnVuIGlzIG9wZW5cblx0ICovXG5cdHByaXZhdGUgZW1pdCAoZmlsZVBhdGg6IHN0cmluZywgY29udGVudDogc3RyaW5nKTogdm9pZCB7XG5cdFx0aWYgKHRoaXMucGVuZGluZykge1xuXHRcdFx0dGhpcy5wZW5kaW5nLnB1c2goeyBmaWxlUGF0aCwgY29udGVudCB9KTtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgY29udGVudCwgJ3V0Zi04Jyk7XG5cdH1cblxuXHQvKipcblx0ICogTGVnYWN5IHdyaXRlIG1ldGhvZCAtIGRlbGVnYXRlcyB0byB3cml0ZVR5cGVzRmlsZVxuXHQgKi9cblx0d3JpdGUgKGdlbmVyYXRlZDogR2VuZXJhdGVkVHlwZXMpOiBzdHJpbmcge1xuXHRcdHJldHVybiB0aGlzLndyaXRlVHlwZXNGaWxlKGdlbmVyYXRlZCk7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgdHlwZXMudHMgZmlsZSAoZXhwb3J0YWJsZSB0eXBlIGFsaWFzZXMgLSBkZWZhdWx0IG1vZGUpXG5cdCAqL1xuXHR3cml0ZVR5cGVzRmlsZSAoZ2VuZXJhdGVkOiBHZW5lcmF0ZWRUeXBlcyk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ3R5cGVzLnRzJyk7XG5cdFx0dGhpcy5lbWl0KGZpbGVQYXRoLCBnZW5lcmF0ZWQuY29udGVudCk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHRvIGEgY3VzdG9tIGZpbGVuYW1lXG5cdCAqL1xuXHR3cml0ZVRvIChmaWxlbmFtZTogc3RyaW5nLCBjb250ZW50OiBzdHJpbmcpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsIGZpbGVuYW1lKTtcblx0XHR0aGlzLmVtaXQoZmlsZVBhdGgsIGNvbnRlbnQpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbnN1cmUgb3V0cHV0IGRpcmVjdG9yeSBleGlzdHNcblx0ICovXG5cdHByaXZhdGUgZW5zdXJlRGlyZWN0b3J5ICgpOiB2b2lkIHtcblx0XHRpZiAoIWZzLmV4aXN0c1N5bmModGhpcy5vdXRwdXREaXIpKSB7XG5cdFx0XHRmcy5ta2RpclN5bmModGhpcy5vdXRwdXREaXIsIHsgcmVjdXJzaXZlIDogdHJ1ZSB9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ2xlYW4gdGhlIG91dHB1dCBkaXJlY3Rvcnlcblx0ICovXG5cdGNsZWFuICgpOiB2b2lkIHtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyh0aGlzLm91dHB1dERpcikpIHtcblx0XHRcdGNvbnN0IGZpbGVzID0gZnMucmVhZGRpclN5bmModGhpcy5vdXRwdXREaXIpO1xuXHRcdFx0Zm9yIChjb25zdCBmaWxlIG9mIGZpbGVzKSB7XG5cdFx0XHRcdGZzLnVubGlua1N5bmMocGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCBmaWxlKSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBvdXRwdXQgZGlyZWN0b3J5XG5cdCAqL1xuXHRnZXRPdXRwdXREaXIgKCk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIHRoaXMub3V0cHV0RGlyO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGRlZmluaXRpb25zLmpzb24gZmlsZS4gV2hlbiB0aGUgdHlwZSBncmFwaCBpcyBwYXNzZWQgKHRoZSBDTElcblx0ICogYWx3YXlzIHBhc3NlcyBpdCksIGVhY2ggZW50cnkgZ2FpbnMgYGZpZWxkc2AgKHRoZSB0eXBlJ3Mgb3duIGZpZWxkcyBpblxuXHQgKiBkZWNsYXJhdGlvbiBvcmRlciwgZnJvbSBUeXBlTm9kZS5wcm9wZXJ0aWVzKSBhbmQgYGFyZ3NgICh0aGVcblx0ICogY29uc3RydWN0b3IncyBwYXJhbWV0ZXJzLCBmcm9tIFR5cGVOb2RlLmNvbnN0cnVjdG9yUGFyYW1zKSDigJQgdGhlIHNhbWVcblx0ICogc291cmNlIG9mIHRydXRoIHR5cGVzLnRzIHJlbmRlcnMuIEEgcmVzdCBwYXJhbWV0ZXIgaXMgZW1pdHRlZCB3aXRoXG5cdCAqIGBraW5kOiAncmVzdCdgIGFuZCBubyBgb3B0aW9uYWxgIChsZXRoZSBkZWZpbml0aW9ucyBjb250cmFjdCk7IGBhcmdzYFxuXHQgKiBpcyBvbWl0dGVkIG9ubHkgd2hlbiBjb25zdHJ1Y3RvclBhcmFtcyB3YXMgbmV2ZXIgZXh0cmFjdGVkLlxuXHQgKi9cblx0d3JpdGVEZWZpbml0aW9uc0ZpbGUgKGRlZmluaXRpb25zOiBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4sIGdyYXBoPzogVHlwZUdyYXBoKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnZGVmaW5pdGlvbnMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZGVmaW5pdGlvbnNPYmo6IFJlY29yZDxzdHJpbmcsIERlZmluaXRpb25JbmZvPiA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgZGVmaW5pdGlvbnMpIHtcblx0XHRcdGRlZmluaXRpb25zT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblxuXHRcdGlmIChncmFwaCkge1xuXHRcdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdFx0XHRjb25zdCBub2RlID0gZ3JhcGguZmluZFR5cGUoa2V5KTtcblx0XHRcdFx0aWYgKCFub2RlKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Ly8gZW5yaWNoIGEgY29weSDigJQgdGhlIGFuYWx5emVyJ3MgZGVmaW5pdGlvbnMgbWFwIHN0YXlzIHVudG91Y2hlZFxuXHRcdFx0XHRjb25zdCBlbnRyeTogRGVmaW5pdGlvbkluZm8gPSB7IC4uLnZhbHVlIH07XG5cdFx0XHRcdGNvbnN0IGZpZWxkczogRGVmaW5pdGlvbkZpZWxkW10gPSBbXTtcblx0XHRcdFx0Zm9yIChjb25zdCBwcm9wSW5mbyBvZiBub2RlLnByb3BlcnRpZXMudmFsdWVzKCkpIHtcblx0XHRcdFx0XHRmaWVsZHMucHVzaCh7XG5cdFx0XHRcdFx0XHRuYW1lICAgICA6IHByb3BJbmZvLm5hbWUsXG5cdFx0XHRcdFx0XHR0eXBlICAgICA6IHByb3BJbmZvLnR5cGUsXG5cdFx0XHRcdFx0XHRvcHRpb25hbCA6IHByb3BJbmZvLm9wdGlvbmFsXG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0ZW50cnkuZmllbGRzID0gZmllbGRzO1xuXHRcdFx0XHRpZiAobm9kZS5jb25zdHJ1Y3RvclBhcmFtcyAhPT0gdW5kZWZpbmVkKSB7XG5cdFx0XHRcdFx0Y29uc3QgYXJnczogRGVmaW5pdGlvbkFyZ1tdID0gbm9kZS5jb25zdHJ1Y3RvclBhcmFtcy5tYXAoKHBhcmFtKSA9PiB7XG5cdFx0XHRcdFx0XHQvLyBhIHJlc3QgcGFyYW1ldGVyIG1heSBhbHdheXMgcmVjZWl2ZSBub3RoaW5nOlxuXHRcdFx0XHRcdFx0Ly8gdGhlIGNvbnRyYWN0IGdpdmVzIGl0IGBraW5kYCBhbmQgbm8gYG9wdGlvbmFsYFxuXHRcdFx0XHRcdFx0Y29uc3QgYXJnOiBEZWZpbml0aW9uQXJnID0gcGFyYW0ua2luZCA9PT0gJ3Jlc3QnXG5cdFx0XHRcdFx0XHRcdD8ge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUgOiBwYXJhbS5uYW1lLFxuXHRcdFx0XHRcdFx0XHRcdHR5cGUgOiBwYXJhbS50eXBlLFxuXHRcdFx0XHRcdFx0XHRcdGtpbmQgOiAncmVzdCdcblx0XHRcdFx0XHRcdFx0fVxuXHRcdFx0XHRcdFx0XHQ6IHtcblx0XHRcdFx0XHRcdFx0XHRuYW1lICAgICA6IHBhcmFtLm5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSAgICAgOiBwYXJhbS50eXBlLFxuXHRcdFx0XHRcdFx0XHRcdG9wdGlvbmFsIDogcGFyYW0ub3B0aW9uYWxcblx0XHRcdFx0XHRcdFx0fTtcblx0XHRcdFx0XHRcdHJldHVybiBhcmc7XG5cdFx0XHRcdFx0fSk7XG5cdFx0XHRcdFx0ZW50cnkuYXJncyA9IGFyZ3M7XG5cdFx0XHRcdH1cblx0XHRcdFx0ZGVmaW5pdGlvbnNPYmpbIGtleSBdID0gZW50cnk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjInLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRkZWZpbml0aW9ucyA6IGRlZmluaXRpb25zT2JqLFxuXHRcdH0pO1xuXG5cdFx0dGhpcy5lbWl0KGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHVzYWdlcy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlVXNhZ2VzRmlsZSAodXNhZ2VzOiBNYXA8c3RyaW5nLCBVc2FnZUluZm9bXT4pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICd1c2FnZXMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgdXNhZ2VzT2JqOiBSZWNvcmQ8c3RyaW5nLCBVc2FnZUluZm9bXT4gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIHVzYWdlcykge1xuXHRcdFx0dXNhZ2VzT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGpzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4yJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0dXNhZ2VzICAgICAgOiB1c2FnZXNPYmosXG5cdFx0fSk7XG5cblx0XHR0aGlzLmVtaXQoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgZWRzLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVFRFNGaWxlIChlZHM6IE1hcDxzdHJpbmcsIEVEU0luZm9bXT4pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdlZHMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZWRzT2JqOiBSZWNvcmQ8c3RyaW5nLCBFRFNJbmZvW10+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBlZHMpIHtcblx0XHRcdGVkc09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMicsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdGVkcyAgICAgICAgIDogZWRzT2JqLFxuXHRcdH0pO1xuXG5cdFx0dGhpcy5lbWl0KGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGluc3RydW1lbnRhdGlvbi5qc29uIGZpbGUgKHYyOiBhZGRzIHRoZSBjcmVhdGlvbkdyYXBoIGtleSB3aGVuXG5cdCAqIHRoZSBjYWxsZXIgcGFzc2VzIGNyZWF0aW9uLWdyYXBoIGRhdGEg4oCUIHRoZSBDTEkgYWx3YXlzIGRvZXMpXG5cdCAqL1xuXHR3cml0ZUluc3RydW1lbnRhdGlvbkZpbGUgKHBvaW50czogSW5zdHJ1bWVudGF0aW9uUG9pbnRbXSwgY3JlYXRpb25HcmFwaD86IENyZWF0aW9uR3JhcGgpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdpbnN0cnVtZW50YXRpb24uanNvbicpO1xuXG5cdFx0Y29uc3QganNvbjogSW5zdHJ1bWVudGF0aW9uSnNvbiA9IHtcblx0XHRcdHZlcnNpb24gICAgIDogMixcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0cG9pbnRzLFxuXHRcdH07XG5cdFx0aWYgKGNyZWF0aW9uR3JhcGgpIHtcblx0XHRcdGpzb24uY3JlYXRpb25HcmFwaCA9IGNyZWF0aW9uR3JhcGg7XG5cdFx0fVxuXG5cdFx0Y29uc3QgcmVsYXRpdml6ZWQgPSB0aGlzLnJlbGF0aXZpemUoanNvbik7XG5cdFx0dGhpcy5lbWl0KGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShyZWxhdGl2aXplZCwgbnVsbCwgMikpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBjb250cm9sLmpzb24gZmlsZSAobGV0aGUgY29udHJhY3QsIGZvcm1hdCAxLjIpOiBgY2FsbGVyc2AgaXMgdGhlXG5cdCAqIGNyZWF0aW9uIGdyYXBoIGluc3RydW1lbnRhdGlvbi5qc29uIHYyIGNhcnJpZXMsIGBwb2ludHNgIHRoZSBzYW1lXG5cdCAqIHBsdWdpbi1zdXBwbGllZCBpbnN0cnVtZW50YXRpb24gcG9pbnRzLiBpbnN0cnVtZW50YXRpb24uanNvbiBrZWVwcyBpdHNcblx0ICogc2hhcGUgZm9yIG1uZW1vZ3JhcGhpY2E7IGNvbnRyb2wuanNvbiBpcyB0aGUgY3Jvc3MtbGFuZ3VhZ2UgY29udHJhY3Rcblx0ICogcmVuZGVyaW5nIG9mIHRoZSBzYW1lIGRhdGEuXG5cdCAqL1xuXHR3cml0ZUNvbnRyb2xGaWxlIChwb2ludHM6IEluc3RydW1lbnRhdGlvblBvaW50W10sIGNhbGxlcnM6IENyZWF0aW9uR3JhcGgpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdjb250cm9sLmpzb24nKTtcblxuXHRcdGNvbnN0IGpzb246IENvbnRyb2xKc29uID0ge1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4yJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0Y2FsbGVycyxcblx0XHRcdHBvaW50cyxcblx0XHR9O1xuXG5cdFx0Y29uc3QgcmVsYXRpdml6ZWQgPSB0aGlzLnJlbGF0aXZpemUoanNvbik7XG5cdFx0dGhpcy5lbWl0KGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShyZWxhdGl2aXplZCwgbnVsbCwgMikpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBmbG93Lmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVGbG93RmlsZSAoZmxvdzogTWFwPHN0cmluZywgRmxvd0luZm9bXT4pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdmbG93Lmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwIHRvIHBsYWluIG9iamVjdFxuXHRcdGNvbnN0IGZsb3dPYmo6IFJlY29yZDxzdHJpbmcsIEZsb3dJbmZvW10+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBmbG93KSB7XG5cdFx0XHRmbG93T2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGpzb246IEZsb3dKc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMicsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdGZsb3cgICAgICAgIDogZmxvd09iaixcblx0XHR9KTtcblxuXHRcdHRoaXMuZW1pdChmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMikpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBtb2R1bGVzLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVNb2R1bGVzRmlsZSAoZ3JhcGg6IE1vZHVsZUdyYXBoKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnbW9kdWxlcy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBtb2R1bGVzT2JqOiBNb2R1bGVzSnNvblsgJ21vZHVsZXMnIF0gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGdyYXBoLm1vZHVsZXMpIHtcblx0XHRcdG1vZHVsZXNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbjogTW9kdWxlc0pzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0bW9kdWxlcyAgICAgOiBtb2R1bGVzT2JqLFxuXHRcdFx0ZWRnZXMgICAgICAgOiBncmFwaC5lZGdlcyxcblx0XHRcdGN5Y2xlcyAgICAgIDogZ3JhcGguY3ljbGVzLFxuXHRcdH0pO1xuXG5cdFx0dGhpcy5lbWl0KGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHNjb3Blcy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlU2NvcGVzRmlsZSAoYW5hbHlzaXM6IFNjb3BlQW5hbHlzaXMpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdzY29wZXMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXBzIHRvIHBsYWluIHNoYXBlc1xuXHRcdGNvbnN0IHNjb3Blc09iajogU2NvcGVzSnNvblsgJ3Njb3BlcycgXSA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgYW5hbHlzaXMuc2NvcGVzKSB7XG5cdFx0XHRzY29wZXNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXHRcdGNvbnN0IHZhcmlhYmxlcyA9IEFycmF5LmZyb20oYW5hbHlzaXMudmFyaWFibGVzLnZhbHVlcygpKTtcblxuXHRcdGNvbnN0IGpzb246IFNjb3Blc0pzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0c2NvcGVzICAgICAgOiBzY29wZXNPYmosXG5cdFx0XHR2YXJpYWJsZXMsXG5cdFx0fSk7XG5cblx0XHR0aGlzLmVtaXQoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgaGllcmFyY2h5Lmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVIaWVyYXJjaHlGaWxlIChyb290czogSGllcmFyY2h5Tm9kZVtdKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnaGllcmFyY2h5Lmpzb24nKTtcblxuXHRcdGNvbnN0IGpzb246IEhpZXJhcmNoeUpzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4yJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0cm9vdHMsXG5cdFx0fSk7XG5cblx0XHR0aGlzLmVtaXQoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgdGhlIGNvbGxlY3Rpb24gbWFuaWZlc3Q6IG9uZSBlbnRyeSBwZXIgY29sbGVjdGlvbiAoZGVmYXVsdFxuXHQgKiBmaXJzdCB3aGVuIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBleGlzdCksIGlkcyArIGRpc3BsYXkgbmFtZXMgK1xuXHQgKiBjYWxsIHNpdGVzICsgbGFuZ3VhZ2UuIFRoZSBgY29sbGVjdGlvbklkOjpgIHByZWZpeCBvbiBncmFwaC1vdXRwdXRcblx0ICogZnVsbFBhdGhzIGpvaW5zIHRvIHRoZSBlbnRyeSBgaWRgLiBGb3JtYXQgMS4yOiB0aGUgcmVnaXN0cnlcblx0ICogaW50ZXJmYWNlIGlzIG5vdCBwYXJ0IG9mIHRoZSBtYW5pZmVzdCDigJQgdGhlIHJlZ2lzdHJ5LXByZWZpeGVkXG5cdCAqIGFsaWFzZXMgaW4gdHlwZXMudHMgLyByZWdpc3RyeS50cyBjb21lIGZyb20gdGhlIGluLW1lbW9yeVxuXHQgKiBUeXBlTm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUgaW5zdGVhZC5cblx0ICovXG5cdHdyaXRlQ29sbGVjdGlvbnNGaWxlIChjb2xsZWN0aW9uczogQ29sbGVjdGlvbk1hbmlmZXN0RW50cnlbXSk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2NvbGxlY3Rpb25zLmpzb24nKTtcblxuXHRcdGNvbnN0IGpzb246IENvbGxlY3Rpb25zSnNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjInLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRjb2xsZWN0aW9ucyxcblx0XHR9KTtcblxuXHRcdHRoaXMuZW1pdChmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMikpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxufVxuIl19