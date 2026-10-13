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
            version: '1.2',
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
            version: '1.2',
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
            version: '1.2',
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
            version: '1.2',
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
            version: '1.2',
            generatedAt: new Date().toISOString(),
            roots,
        });
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
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
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
}
exports.TypesWriter = TypesWriter;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoid3JpdGVyLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL3dyaXRlci50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLHVDQUF5QjtBQUN6QiwyQ0FBNkI7QUFPN0I7O0dBRUc7QUFDSCxNQUFhLFdBQVc7SUFJdkIsWUFBYSxTQUFTLEdBQUcsVUFBVSxFQUFFLFdBQW9CO1FBQ3hELElBQUksQ0FBQyxTQUFTLEdBQUcsU0FBUyxDQUFDO1FBQzNCLElBQUksQ0FBQyxXQUFXLEdBQUcsV0FBVyxLQUFLLFNBQVM7WUFDM0MsQ0FBQyxDQUFDLFNBQVM7WUFDWCxDQUFDLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxXQUFXLENBQUMsQ0FBQztJQUM5QixDQUFDO0lBRUQ7Ozs7Ozs7T0FPRztJQUNLLFVBQVUsQ0FBSyxPQUFVO1FBQ2hDLElBQUksSUFBSSxDQUFDLFdBQVcsS0FBSyxTQUFTLEVBQUUsQ0FBQztZQUNwQyxPQUFPLE9BQU8sQ0FBQztRQUNoQixDQUFDO1FBQ0QsTUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFdBQVcsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO1FBQzNDLE1BQU0sSUFBSSxHQUFHLENBQUMsS0FBYyxFQUFXLEVBQUU7WUFDeEMsSUFBSSxPQUFPLEtBQUssS0FBSyxRQUFRLEVBQUUsQ0FBQztnQkFDL0IsSUFBSSxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztvQkFDL0IsT0FBTyxLQUFLLENBQUM7Z0JBQ2QsQ0FBQztnQkFDRCxNQUFNLFFBQVEsR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQztnQkFDNUMsTUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO2dCQUNsRCxPQUFPLE1BQU0sQ0FBQztZQUNmLENBQUM7WUFDRCxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQztnQkFDMUIsTUFBTSxNQUFNLEdBQUcsS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztnQkFDL0IsT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1lBQ0QsSUFBSSxLQUFLLEtBQUssSUFBSSxJQUFJLE9BQU8sS0FBSyxLQUFLLFFBQVEsRUFBRSxDQUFDO2dCQUNqRCxNQUFNLE1BQU0sR0FBNEIsRUFBRSxDQUFDO2dCQUMzQyxLQUFLLE1BQU0sQ0FBRSxHQUFHLEVBQUUsS0FBSyxDQUFFLElBQUksTUFBTSxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsRUFBRSxDQUFDO29CQUNwRCxNQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFXLENBQUM7b0JBQ3RDLE1BQU0sQ0FBRSxTQUFTLENBQUUsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7Z0JBQ25DLENBQUM7Z0JBQ0QsT0FBTyxNQUFNLENBQUM7WUFDZixDQUFDO1lBQ0QsT0FBTyxLQUFLLENBQUM7UUFDZCxDQUFDLENBQUM7UUFDRixNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsT0FBTyxDQUFDLENBQUM7UUFDN0IsT0FBTyxNQUFXLENBQUM7SUFDcEIsQ0FBQztJQUVEOztPQUVHO0lBQ0gsS0FBSyxDQUFFLFNBQXlCO1FBQy9CLE9BQU8sSUFBSSxDQUFDLGNBQWMsQ0FBQyxTQUFTLENBQUMsQ0FBQztJQUN2QyxDQUFDO0lBRUQ7O09BRUc7SUFDSCxjQUFjLENBQUUsU0FBeUI7UUFDeEMsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1FBQ3ZCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxVQUFVLENBQUMsQ0FBQztRQUN2RCxFQUFFLENBQUMsYUFBYSxDQUFDLFFBQVEsRUFBRSxTQUFTLENBQUMsT0FBTyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ3ZELE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7SUFFRDs7T0FFRztJQUNILHVCQUF1QixDQUFFLFNBQXlCO1FBQ2pELElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztRQUN2QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsWUFBWSxDQUFDLENBQUM7UUFDekQsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsU0FBUyxDQUFDLE9BQU8sRUFBRSxPQUFPLENBQUMsQ0FBQztRQUN2RCxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0lBRUQ7O09BRUc7SUFDSCxPQUFPLENBQUUsUUFBZ0IsRUFBRSxPQUFlO1FBQ3pDLElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztRQUN2QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsUUFBUSxDQUFDLENBQUM7UUFDckQsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsT0FBTyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQzdDLE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7SUFFRDs7T0FFRztJQUNLLGVBQWU7UUFDdEIsSUFBSSxDQUFDLEVBQUUsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxFQUFFLENBQUM7WUFDcEMsRUFBRSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLEVBQUUsU0FBUyxFQUFHLElBQUksRUFBRSxDQUFDLENBQUM7UUFDcEQsQ0FBQztJQUNGLENBQUM7SUFFRDs7T0FFRztJQUNILEtBQUs7UUFDSixJQUFJLEVBQUUsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxFQUFFLENBQUM7WUFDbkMsTUFBTSxLQUFLLEdBQUcsRUFBRSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7WUFDN0MsS0FBSyxNQUFNLElBQUksSUFBSSxLQUFLLEVBQUUsQ0FBQztnQkFDMUIsRUFBRSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsSUFBSSxDQUFDLENBQUMsQ0FBQztZQUNoRCxDQUFDO1FBQ0YsQ0FBQztJQUNGLENBQUM7SUFFRDs7T0FFRztJQUNILFlBQVk7UUFDWCxPQUFPLElBQUksQ0FBQyxTQUFTLENBQUM7SUFDdkIsQ0FBQztJQUVEOzs7Ozs7OztPQVFHO0lBQ0gsb0JBQW9CLENBQUUsV0FBd0MsRUFBRSxLQUFpQjtRQUNoRixJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7UUFDdkIsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLGtCQUFrQixDQUFDLENBQUM7UUFFL0QsOEJBQThCO1FBQzlCLE1BQU0sY0FBYyxHQUFtQyxFQUFFLENBQUM7UUFDMUQsS0FBSyxNQUFNLENBQUUsR0FBRyxFQUFFLEtBQUssQ0FBRSxJQUFJLFdBQVcsRUFBRSxDQUFDO1lBQzFDLGNBQWMsQ0FBRSxHQUFHLENBQUUsR0FBRyxLQUFLLENBQUM7UUFDL0IsQ0FBQztRQUVELElBQUksS0FBSyxFQUFFLENBQUM7WUFDWCxLQUFLLE1BQU0sQ0FBRSxHQUFHLEVBQUUsS0FBSyxDQUFFLElBQUksV0FBVyxFQUFFLENBQUM7Z0JBQzFDLE1BQU0sSUFBSSxHQUFHLEtBQUssQ0FBQyxRQUFRLENBQUMsR0FBRyxDQUFDLENBQUM7Z0JBQ2pDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztvQkFDWCxTQUFTO2dCQUNWLENBQUM7Z0JBQ0QsaUVBQWlFO2dCQUNqRSxNQUFNLEtBQUssR0FBbUIsRUFBRSxHQUFHLEtBQUssRUFBRSxDQUFDO2dCQUMzQyxNQUFNLE1BQU0sR0FBc0IsRUFBRSxDQUFDO2dCQUNyQyxLQUFLLE1BQU0sUUFBUSxJQUFJLElBQUksQ0FBQyxVQUFVLENBQUMsTUFBTSxFQUFFLEVBQUUsQ0FBQztvQkFDakQsTUFBTSxDQUFDLElBQUksQ0FBQzt3QkFDWCxJQUFJLEVBQU8sUUFBUSxDQUFDLElBQUk7d0JBQ3hCLElBQUksRUFBTyxRQUFRLENBQUMsSUFBSTt3QkFDeEIsUUFBUSxFQUFHLFFBQVEsQ0FBQyxRQUFRO3FCQUM1QixDQUFDLENBQUM7Z0JBQ0osQ0FBQztnQkFDRCxLQUFLLENBQUMsTUFBTSxHQUFHLE1BQU0sQ0FBQztnQkFDdEIsSUFBSSxJQUFJLENBQUMsaUJBQWlCLEtBQUssU0FBUyxFQUFFLENBQUM7b0JBQzFDLE1BQU0sSUFBSSxHQUFvQixJQUFJLENBQUMsaUJBQWlCLENBQUMsR0FBRyxDQUFDLENBQUMsS0FBSyxFQUFFLEVBQUU7d0JBQ2xFLCtDQUErQzt3QkFDL0MsaURBQWlEO3dCQUNqRCxNQUFNLEdBQUcsR0FBa0IsS0FBSyxDQUFDLElBQUksS0FBSyxNQUFNOzRCQUMvQyxDQUFDLENBQUM7Z0NBQ0QsSUFBSSxFQUFHLEtBQUssQ0FBQyxJQUFJO2dDQUNqQixJQUFJLEVBQUcsS0FBSyxDQUFDLElBQUk7Z0NBQ2pCLElBQUksRUFBRyxNQUFNOzZCQUNiOzRCQUNELENBQUMsQ0FBQztnQ0FDRCxJQUFJLEVBQU8sS0FBSyxDQUFDLElBQUk7Z0NBQ3JCLElBQUksRUFBTyxLQUFLLENBQUMsSUFBSTtnQ0FDckIsUUFBUSxFQUFHLEtBQUssQ0FBQyxRQUFROzZCQUN6QixDQUFDO3dCQUNILE9BQU8sR0FBRyxDQUFDO29CQUNaLENBQUMsQ0FBQyxDQUFDO29CQUNILEtBQUssQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO2dCQUNuQixDQUFDO2dCQUNELGNBQWMsQ0FBRSxHQUFHLENBQUUsR0FBRyxLQUFLLENBQUM7WUFDL0IsQ0FBQztRQUNGLENBQUM7UUFFRCxNQUFNLElBQUksR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDO1lBQzVCLE9BQU8sRUFBTyxLQUFLO1lBQ25CLFdBQVcsRUFBRyxJQUFJLElBQUksRUFBRSxDQUFDLFdBQVcsRUFBRTtZQUN0QyxXQUFXLEVBQUcsY0FBYztTQUM1QixDQUFDLENBQUM7UUFFSCxFQUFFLENBQUMsYUFBYSxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxJQUFJLEVBQUUsQ0FBQyxDQUFDLEVBQUUsT0FBTyxDQUFDLENBQUM7UUFDbkUsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOztPQUVHO0lBQ0gsZUFBZSxDQUFFLE1BQWdDO1FBQ2hELElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztRQUN2QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsYUFBYSxDQUFDLENBQUM7UUFFMUQsOEJBQThCO1FBQzlCLE1BQU0sU0FBUyxHQUFnQyxFQUFFLENBQUM7UUFDbEQsS0FBSyxNQUFNLENBQUUsR0FBRyxFQUFFLEtBQUssQ0FBRSxJQUFJLE1BQU0sRUFBRSxDQUFDO1lBQ3JDLFNBQVMsQ0FBRSxHQUFHLENBQUUsR0FBRyxLQUFLLENBQUM7UUFDMUIsQ0FBQztRQUVELE1BQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUM7WUFDNUIsT0FBTyxFQUFPLEtBQUs7WUFDbkIsV0FBVyxFQUFHLElBQUksSUFBSSxFQUFFLENBQUMsV0FBVyxFQUFFO1lBQ3RDLE1BQU0sRUFBUSxTQUFTO1NBQ3ZCLENBQUMsQ0FBQztRQUVILEVBQUUsQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxDQUFDLENBQUMsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUNuRSxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0lBRUQ7O09BRUc7SUFDSCxZQUFZLENBQUUsR0FBMkI7UUFDeEMsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1FBQ3ZCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxVQUFVLENBQUMsQ0FBQztRQUV2RCw4QkFBOEI7UUFDOUIsTUFBTSxNQUFNLEdBQThCLEVBQUUsQ0FBQztRQUM3QyxLQUFLLE1BQU0sQ0FBRSxHQUFHLEVBQUUsS0FBSyxDQUFFLElBQUksR0FBRyxFQUFFLENBQUM7WUFDbEMsTUFBTSxDQUFFLEdBQUcsQ0FBRSxHQUFHLEtBQUssQ0FBQztRQUN2QixDQUFDO1FBRUQsTUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQztZQUM1QixPQUFPLEVBQU8sS0FBSztZQUNuQixXQUFXLEVBQUcsSUFBSSxJQUFJLEVBQUUsQ0FBQyxXQUFXLEVBQUU7WUFDdEMsR0FBRyxFQUFXLE1BQU07U0FDcEIsQ0FBQyxDQUFDO1FBRUgsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ25FLE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7SUFFRDs7O09BR0c7SUFDSCx3QkFBd0IsQ0FBRSxNQUE4QixFQUFFLGFBQTZCO1FBQ3RGLElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztRQUN2QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsc0JBQXNCLENBQUMsQ0FBQztRQUVuRSxNQUFNLElBQUksR0FBd0I7WUFDakMsT0FBTyxFQUFPLENBQUM7WUFDZixXQUFXLEVBQUcsSUFBSSxJQUFJLEVBQUUsQ0FBQyxXQUFXLEVBQUU7WUFDdEMsTUFBTTtTQUNOLENBQUM7UUFDRixJQUFJLGFBQWEsRUFBRSxDQUFDO1lBQ25CLElBQUksQ0FBQyxhQUFhLEdBQUcsYUFBYSxDQUFDO1FBQ3BDLENBQUM7UUFFRCxNQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxDQUFDO1FBQzFDLEVBQUUsQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUMsV0FBVyxFQUFFLElBQUksRUFBRSxDQUFDLENBQUMsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUMxRSxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0lBRUQ7Ozs7OztPQU1HO0lBQ0gsZ0JBQWdCLENBQUUsTUFBOEIsRUFBRSxPQUFzQjtRQUN2RSxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7UUFDdkIsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLGNBQWMsQ0FBQyxDQUFDO1FBRTNELE1BQU0sSUFBSSxHQUFnQjtZQUN6QixPQUFPLEVBQU8sS0FBSztZQUNuQixXQUFXLEVBQUcsSUFBSSxJQUFJLEVBQUUsQ0FBQyxXQUFXLEVBQUU7WUFDdEMsT0FBTztZQUNQLE1BQU07U0FDTixDQUFDO1FBRUYsTUFBTSxXQUFXLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsQ0FBQztRQUMxQyxFQUFFLENBQUMsYUFBYSxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMsU0FBUyxDQUFDLFdBQVcsRUFBRSxJQUFJLEVBQUUsQ0FBQyxDQUFDLEVBQUUsT0FBTyxDQUFDLENBQUM7UUFDMUUsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOztPQUVHO0lBQ0gsYUFBYSxDQUFFLElBQTZCO1FBQzNDLElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztRQUN2QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsV0FBVyxDQUFDLENBQUM7UUFFeEQsOEJBQThCO1FBQzlCLE1BQU0sT0FBTyxHQUErQixFQUFFLENBQUM7UUFDL0MsS0FBSyxNQUFNLENBQUUsR0FBRyxFQUFFLEtBQUssQ0FBRSxJQUFJLElBQUksRUFBRSxDQUFDO1lBQ25DLE9BQU8sQ0FBRSxHQUFHLENBQUUsR0FBRyxLQUFLLENBQUM7UUFDeEIsQ0FBQztRQUVELE1BQU0sSUFBSSxHQUFhLElBQUksQ0FBQyxVQUFVLENBQUM7WUFDdEMsT0FBTyxFQUFPLEtBQUs7WUFDbkIsV0FBVyxFQUFHLElBQUksSUFBSSxFQUFFLENBQUMsV0FBVyxFQUFFO1lBQ3RDLElBQUksRUFBVSxPQUFPO1NBQ3JCLENBQUMsQ0FBQztRQUVILEVBQUUsQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxDQUFDLENBQUMsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUNuRSxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0lBRUQ7O09BRUc7SUFDSCxnQkFBZ0IsQ0FBRSxLQUFrQjtRQUNuQyxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7UUFDdkIsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLGNBQWMsQ0FBQyxDQUFDO1FBRTNELDhCQUE4QjtRQUM5QixNQUFNLFVBQVUsR0FBNkIsRUFBRSxDQUFDO1FBQ2hELEtBQUssTUFBTSxDQUFFLEdBQUcsRUFBRSxLQUFLLENBQUUsSUFBSSxLQUFLLENBQUMsT0FBTyxFQUFFLENBQUM7WUFDNUMsVUFBVSxDQUFFLEdBQUcsQ0FBRSxHQUFHLEtBQUssQ0FBQztRQUMzQixDQUFDO1FBRUQsTUFBTSxJQUFJLEdBQWdCLElBQUksQ0FBQyxVQUFVLENBQUM7WUFDekMsT0FBTyxFQUFPLEtBQUs7WUFDbkIsV0FBVyxFQUFHLElBQUksSUFBSSxFQUFFLENBQUMsV0FBVyxFQUFFO1lBQ3RDLE9BQU8sRUFBTyxVQUFVO1lBQ3hCLEtBQUssRUFBUyxLQUFLLENBQUMsS0FBSztZQUN6QixNQUFNLEVBQVEsS0FBSyxDQUFDLE1BQU07U0FDMUIsQ0FBQyxDQUFDO1FBRUgsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ25FLE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7SUFFRDs7T0FFRztJQUNILGVBQWUsQ0FBRSxRQUF1QjtRQUN2QyxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7UUFDdkIsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLGFBQWEsQ0FBQyxDQUFDO1FBRTFELCtCQUErQjtRQUMvQixNQUFNLFNBQVMsR0FBMkIsRUFBRSxDQUFDO1FBQzdDLEtBQUssTUFBTSxDQUFFLEdBQUcsRUFBRSxLQUFLLENBQUUsSUFBSSxRQUFRLENBQUMsTUFBTSxFQUFFLENBQUM7WUFDOUMsU0FBUyxDQUFFLEdBQUcsQ0FBRSxHQUFHLEtBQUssQ0FBQztRQUMxQixDQUFDO1FBQ0QsTUFBTSxTQUFTLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsU0FBUyxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUM7UUFFMUQsTUFBTSxJQUFJLEdBQWUsSUFBSSxDQUFDLFVBQVUsQ0FBQztZQUN4QyxPQUFPLEVBQU8sS0FBSztZQUNuQixXQUFXLEVBQUcsSUFBSSxJQUFJLEVBQUUsQ0FBQyxXQUFXLEVBQUU7WUFDdEMsTUFBTSxFQUFRLFNBQVM7WUFDdkIsU0FBUztTQUNULENBQUMsQ0FBQztRQUVILEVBQUUsQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxDQUFDLENBQUMsRUFBRSxPQUFPLENBQUMsQ0FBQztRQUNuRSxPQUFPLFFBQVEsQ0FBQztJQUNqQixDQUFDO0lBRUQ7O09BRUc7SUFDSCxrQkFBa0IsQ0FBRSxLQUFzQjtRQUN6QyxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7UUFDdkIsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLGdCQUFnQixDQUFDLENBQUM7UUFFN0QsTUFBTSxJQUFJLEdBQWtCLElBQUksQ0FBQyxVQUFVLENBQUM7WUFDM0MsT0FBTyxFQUFPLEtBQUs7WUFDbkIsV0FBVyxFQUFHLElBQUksSUFBSSxFQUFFLENBQUMsV0FBVyxFQUFFO1lBQ3RDLEtBQUs7U0FDTCxDQUFDLENBQUM7UUFFSCxFQUFFLENBQUMsYUFBYSxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxJQUFJLEVBQUUsQ0FBQyxDQUFDLEVBQUUsT0FBTyxDQUFDLENBQUM7UUFDbkUsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOzs7Ozs7OztPQVFHO0lBQ0gsb0JBQW9CLENBQUUsV0FBc0M7UUFDM0QsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1FBQ3ZCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxrQkFBa0IsQ0FBQyxDQUFDO1FBRS9ELE1BQU0sSUFBSSxHQUFvQixJQUFJLENBQUMsVUFBVSxDQUFDO1lBQzdDLE9BQU8sRUFBTyxLQUFLO1lBQ25CLFdBQVcsRUFBRyxJQUFJLElBQUksRUFBRSxDQUFDLFdBQVcsRUFBRTtZQUN0QyxXQUFXO1NBQ1gsQ0FBQyxDQUFDO1FBRUgsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ25FLE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7Q0FDRDtBQXBZRCxrQ0FvWUMiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIGZzIGZyb20gJ2ZzJztcbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQge1xuXHRHZW5lcmF0ZWRUeXBlcywgRGVmaW5pdGlvbkluZm8sIFVzYWdlSW5mbywgRURTSW5mbywgRmxvd0luZm8sIEZsb3dKc29uLCBIaWVyYXJjaHlOb2RlLCBIaWVyYXJjaHlKc29uLFxuXHRJbnN0cnVtZW50YXRpb25Qb2ludCwgSW5zdHJ1bWVudGF0aW9uSnNvbiwgTW9kdWxlR3JhcGgsIE1vZHVsZXNKc29uLCBTY29wZUFuYWx5c2lzLCBTY29wZXNKc29uLCBDcmVhdGlvbkdyYXBoLFxuXHRDb2xsZWN0aW9uTWFuaWZlc3RFbnRyeSwgQ29sbGVjdGlvbnNKc29uLCBDb250cm9sSnNvbiwgVHlwZUdyYXBoLCBEZWZpbml0aW9uRmllbGQsIERlZmluaXRpb25Bcmdcbn0gZnJvbSAnLi90eXBlcyc7XG5cbi8qKlxuICogV3JpdGVzIGdlbmVyYXRlZCB0eXBlcyB0byBmaWxlIHN5c3RlbVxuICovXG5leHBvcnQgY2xhc3MgVHlwZXNXcml0ZXIge1xuXHRwcml2YXRlIG91dHB1dERpcjogc3RyaW5nO1xuXHRwcml2YXRlIHByb2plY3RSb290Pzogc3RyaW5nO1xuXG5cdGNvbnN0cnVjdG9yIChvdXRwdXREaXIgPSAnLnRhY3RpY2EnLCBwcm9qZWN0Um9vdD86IHN0cmluZykge1xuXHRcdHRoaXMub3V0cHV0RGlyID0gb3V0cHV0RGlyO1xuXHRcdHRoaXMucHJvamVjdFJvb3QgPSBwcm9qZWN0Um9vdCA9PT0gdW5kZWZpbmVkXG5cdFx0XHQ/IHVuZGVmaW5lZFxuXHRcdFx0OiBwYXRoLnJlc29sdmUocHJvamVjdFJvb3QpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFJld3JpdGUgZXZlcnkgcHJvamVjdC1yb290ZWQgYWJzb2x1dGUgcGF0aCBpbiB0aGUgcGF5bG9hZCB0byBhXG5cdCAqIHByb2plY3QtcmVsYXRpdmUgb25lICh2YWx1ZXMgQU5EIG9iamVjdCBrZXlzKSwgc28gLnRhY3RpY2Egb3V0cHV0XG5cdCAqIHN0YXlzIHBvcnRhYmxlIGFjcm9zcyBtYWNoaW5lcyBhbmQgY2hlY2tvdXRzLiBQYXRocyBvdXRzaWRlIHRoZVxuXHQgKiBwcm9qZWN0IHJvb3Qga2VlcCB0aGVpciBhYnNvbHV0ZSBmb3JtIOKAlCB0aGV5IGdlbnVpbmVseSBhcmVcblx0ICogbWFjaGluZS1zcGVjaWZpYy4gQ29uc3VtZXJzIHJlc29sdmUgcmVsYXRpdmUgZW50cmllcyBhZ2FpbnN0IHRoZVxuXHQgKiBkaXJlY3RvcnkgdGhhdCBob2xkcyAudGFjdGljYS5cblx0ICovXG5cdHByaXZhdGUgcmVsYXRpdml6ZTxUPiAocGF5bG9hZDogVCk6IFQge1xuXHRcdGlmICh0aGlzLnByb2plY3RSb290ID09PSB1bmRlZmluZWQpIHtcblx0XHRcdHJldHVybiBwYXlsb2FkO1xuXHRcdH1cblx0XHRjb25zdCBwcmVmaXggPSB0aGlzLnByb2plY3RSb290ICsgcGF0aC5zZXA7XG5cdFx0Y29uc3Qgd2FsayA9IChpbnB1dDogdW5rbm93bik6IHVua25vd24gPT4ge1xuXHRcdFx0aWYgKHR5cGVvZiBpbnB1dCA9PT0gJ3N0cmluZycpIHtcblx0XHRcdFx0aWYgKCFpbnB1dC5zdGFydHNXaXRoKHByZWZpeCkpIHtcblx0XHRcdFx0XHRyZXR1cm4gaW5wdXQ7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgcmVsYXRpdmUgPSBpbnB1dC5zbGljZShwcmVmaXgubGVuZ3RoKTtcblx0XHRcdFx0Y29uc3Qgd2Fsa2VkID0gcmVsYXRpdmUuc3BsaXQocGF0aC5zZXApLmpvaW4oJy8nKTtcblx0XHRcdFx0cmV0dXJuIHdhbGtlZDtcblx0XHRcdH1cblx0XHRcdGlmIChBcnJheS5pc0FycmF5KGlucHV0KSkge1xuXHRcdFx0XHRjb25zdCB3YWxrZWQgPSBpbnB1dC5tYXAod2Fsayk7XG5cdFx0XHRcdHJldHVybiB3YWxrZWQ7XG5cdFx0XHR9XG5cdFx0XHRpZiAoaW5wdXQgIT09IG51bGwgJiYgdHlwZW9mIGlucHV0ID09PSAnb2JqZWN0Jykge1xuXHRcdFx0XHRjb25zdCB3YWxrZWQ6IFJlY29yZDxzdHJpbmcsIHVua25vd24+ID0ge307XG5cdFx0XHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgT2JqZWN0LmVudHJpZXMoaW5wdXQpKSB7XG5cdFx0XHRcdFx0Y29uc3Qgd2Fsa2VkS2V5ID0gd2FsayhrZXkpIGFzIHN0cmluZztcblx0XHRcdFx0XHR3YWxrZWRbIHdhbGtlZEtleSBdID0gd2Fsayh2YWx1ZSk7XG5cdFx0XHRcdH1cblx0XHRcdFx0cmV0dXJuIHdhbGtlZDtcblx0XHRcdH1cblx0XHRcdHJldHVybiBpbnB1dDtcblx0XHR9O1xuXHRcdGNvbnN0IHJlc3VsdCA9IHdhbGsocGF5bG9hZCk7XG5cdFx0cmV0dXJuIHJlc3VsdCBhcyBUO1xuXHR9XG5cblx0LyoqXG5cdCAqIExlZ2FjeSB3cml0ZSBtZXRob2QgLSBkZWxlZ2F0ZXMgdG8gd3JpdGVUeXBlc0ZpbGVcblx0ICovXG5cdHdyaXRlIChnZW5lcmF0ZWQ6IEdlbmVyYXRlZFR5cGVzKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gdGhpcy53cml0ZVR5cGVzRmlsZShnZW5lcmF0ZWQpO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHR5cGVzLnRzIGZpbGUgKGV4cG9ydGFibGUgdHlwZSBhbGlhc2VzIC0gZGVmYXVsdCBtb2RlKVxuXHQgKi9cblx0d3JpdGVUeXBlc0ZpbGUgKGdlbmVyYXRlZDogR2VuZXJhdGVkVHlwZXMpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICd0eXBlcy50cycpO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIGdlbmVyYXRlZC5jb250ZW50LCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgZ2xvYmFsIGF1Z21lbnRhdGlvbiBmaWxlIChpbmRleC5kLnRzIC0gbW9kdWxlIGF1Z21lbnRhdGlvbiBtb2RlKVxuXHQgKi9cblx0d3JpdGVHbG9iYWxBdWdtZW50YXRpb24gKGdlbmVyYXRlZDogR2VuZXJhdGVkVHlwZXMpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdpbmRleC5kLnRzJyk7XG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgZ2VuZXJhdGVkLmNvbnRlbnQsICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB0byBhIGN1c3RvbSBmaWxlbmFtZVxuXHQgKi9cblx0d3JpdGVUbyAoZmlsZW5hbWU6IHN0cmluZywgY29udGVudDogc3RyaW5nKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCBmaWxlbmFtZSk7XG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgY29udGVudCwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIEVuc3VyZSBvdXRwdXQgZGlyZWN0b3J5IGV4aXN0c1xuXHQgKi9cblx0cHJpdmF0ZSBlbnN1cmVEaXJlY3RvcnkgKCk6IHZvaWQge1xuXHRcdGlmICghZnMuZXhpc3RzU3luYyh0aGlzLm91dHB1dERpcikpIHtcblx0XHRcdGZzLm1rZGlyU3luYyh0aGlzLm91dHB1dERpciwgeyByZWN1cnNpdmUgOiB0cnVlIH0pO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDbGVhbiB0aGUgb3V0cHV0IGRpcmVjdG9yeVxuXHQgKi9cblx0Y2xlYW4gKCk6IHZvaWQge1xuXHRcdGlmIChmcy5leGlzdHNTeW5jKHRoaXMub3V0cHV0RGlyKSkge1xuXHRcdFx0Y29uc3QgZmlsZXMgPSBmcy5yZWFkZGlyU3luYyh0aGlzLm91dHB1dERpcik7XG5cdFx0XHRmb3IgKGNvbnN0IGZpbGUgb2YgZmlsZXMpIHtcblx0XHRcdFx0ZnMudW5saW5rU3luYyhwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsIGZpbGUpKTtcblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogR2V0IG91dHB1dCBkaXJlY3Rvcnlcblx0ICovXG5cdGdldE91dHB1dERpciAoKTogc3RyaW5nIHtcblx0XHRyZXR1cm4gdGhpcy5vdXRwdXREaXI7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgZGVmaW5pdGlvbnMuanNvbiBmaWxlLiBXaGVuIHRoZSB0eXBlIGdyYXBoIGlzIHBhc3NlZCAodGhlIENMSVxuXHQgKiBhbHdheXMgcGFzc2VzIGl0KSwgZWFjaCBlbnRyeSBnYWlucyBgZmllbGRzYCAodGhlIHR5cGUncyBvd24gZmllbGRzIGluXG5cdCAqIGRlY2xhcmF0aW9uIG9yZGVyLCBmcm9tIFR5cGVOb2RlLnByb3BlcnRpZXMpIGFuZCBgYXJnc2AgKHRoZVxuXHQgKiBjb25zdHJ1Y3RvcidzIHBhcmFtZXRlcnMsIGZyb20gVHlwZU5vZGUuY29uc3RydWN0b3JQYXJhbXMpIOKAlCB0aGUgc2FtZVxuXHQgKiBzb3VyY2Ugb2YgdHJ1dGggdHlwZXMudHMgcmVuZGVycy4gQSByZXN0IHBhcmFtZXRlciBpcyBlbWl0dGVkIHdpdGhcblx0ICogYGtpbmQ6ICdyZXN0J2AgYW5kIG5vIGBvcHRpb25hbGAgKGxldGhlIGRlZmluaXRpb25zIGNvbnRyYWN0KTsgYGFyZ3NgXG5cdCAqIGlzIG9taXR0ZWQgb25seSB3aGVuIGNvbnN0cnVjdG9yUGFyYW1zIHdhcyBuZXZlciBleHRyYWN0ZWQuXG5cdCAqL1xuXHR3cml0ZURlZmluaXRpb25zRmlsZSAoZGVmaW5pdGlvbnM6IE1hcDxzdHJpbmcsIERlZmluaXRpb25JbmZvPiwgZ3JhcGg/OiBUeXBlR3JhcGgpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdkZWZpbml0aW9ucy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBkZWZpbml0aW9uc09iajogUmVjb3JkPHN0cmluZywgRGVmaW5pdGlvbkluZm8+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdFx0ZGVmaW5pdGlvbnNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0aWYgKGdyYXBoKSB7XG5cdFx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGRlZmluaXRpb25zKSB7XG5cdFx0XHRcdGNvbnN0IG5vZGUgPSBncmFwaC5maW5kVHlwZShrZXkpO1xuXHRcdFx0XHRpZiAoIW5vZGUpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBlbnJpY2ggYSBjb3B5IOKAlCB0aGUgYW5hbHl6ZXIncyBkZWZpbml0aW9ucyBtYXAgc3RheXMgdW50b3VjaGVkXG5cdFx0XHRcdGNvbnN0IGVudHJ5OiBEZWZpbml0aW9uSW5mbyA9IHsgLi4udmFsdWUgfTtcblx0XHRcdFx0Y29uc3QgZmllbGRzOiBEZWZpbml0aW9uRmllbGRbXSA9IFtdO1xuXHRcdFx0XHRmb3IgKGNvbnN0IHByb3BJbmZvIG9mIG5vZGUucHJvcGVydGllcy52YWx1ZXMoKSkge1xuXHRcdFx0XHRcdGZpZWxkcy5wdXNoKHtcblx0XHRcdFx0XHRcdG5hbWUgICAgIDogcHJvcEluZm8ubmFtZSxcblx0XHRcdFx0XHRcdHR5cGUgICAgIDogcHJvcEluZm8udHlwZSxcblx0XHRcdFx0XHRcdG9wdGlvbmFsIDogcHJvcEluZm8ub3B0aW9uYWxcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0fVxuXHRcdFx0XHRlbnRyeS5maWVsZHMgPSBmaWVsZHM7XG5cdFx0XHRcdGlmIChub2RlLmNvbnN0cnVjdG9yUGFyYW1zICE9PSB1bmRlZmluZWQpIHtcblx0XHRcdFx0XHRjb25zdCBhcmdzOiBEZWZpbml0aW9uQXJnW10gPSBub2RlLmNvbnN0cnVjdG9yUGFyYW1zLm1hcCgocGFyYW0pID0+IHtcblx0XHRcdFx0XHRcdC8vIGEgcmVzdCBwYXJhbWV0ZXIgbWF5IGFsd2F5cyByZWNlaXZlIG5vdGhpbmc6XG5cdFx0XHRcdFx0XHQvLyB0aGUgY29udHJhY3QgZ2l2ZXMgaXQgYGtpbmRgIGFuZCBubyBgb3B0aW9uYWxgXG5cdFx0XHRcdFx0XHRjb25zdCBhcmc6IERlZmluaXRpb25BcmcgPSBwYXJhbS5raW5kID09PSAncmVzdCdcblx0XHRcdFx0XHRcdFx0PyB7XG5cdFx0XHRcdFx0XHRcdFx0bmFtZSA6IHBhcmFtLm5hbWUsXG5cdFx0XHRcdFx0XHRcdFx0dHlwZSA6IHBhcmFtLnR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0a2luZCA6ICdyZXN0J1xuXHRcdFx0XHRcdFx0XHR9XG5cdFx0XHRcdFx0XHRcdDoge1xuXHRcdFx0XHRcdFx0XHRcdG5hbWUgICAgIDogcGFyYW0ubmFtZSxcblx0XHRcdFx0XHRcdFx0XHR0eXBlICAgICA6IHBhcmFtLnR5cGUsXG5cdFx0XHRcdFx0XHRcdFx0b3B0aW9uYWwgOiBwYXJhbS5vcHRpb25hbFxuXHRcdFx0XHRcdFx0XHR9O1xuXHRcdFx0XHRcdFx0cmV0dXJuIGFyZztcblx0XHRcdFx0XHR9KTtcblx0XHRcdFx0XHRlbnRyeS5hcmdzID0gYXJncztcblx0XHRcdFx0fVxuXHRcdFx0XHRkZWZpbml0aW9uc09ialsga2V5IF0gPSBlbnRyeTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRjb25zdCBqc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMicsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdGRlZmluaXRpb25zIDogZGVmaW5pdGlvbnNPYmosXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHVzYWdlcy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlVXNhZ2VzRmlsZSAodXNhZ2VzOiBNYXA8c3RyaW5nLCBVc2FnZUluZm9bXT4pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICd1c2FnZXMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgdXNhZ2VzT2JqOiBSZWNvcmQ8c3RyaW5nLCBVc2FnZUluZm9bXT4gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIHVzYWdlcykge1xuXHRcdFx0dXNhZ2VzT2JqWyBrZXkgXSA9IHZhbHVlO1xuXHRcdH1cblxuXHRcdGNvbnN0IGpzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4yJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0dXNhZ2VzICAgICAgOiB1c2FnZXNPYmosXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGVkcy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlRURTRmlsZSAoZWRzOiBNYXA8c3RyaW5nLCBFRFNJbmZvW10+KTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnZWRzLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwIHRvIHBsYWluIG9iamVjdFxuXHRcdGNvbnN0IGVkc09iajogUmVjb3JkPHN0cmluZywgRURTSW5mb1tdPiA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgZWRzKSB7XG5cdFx0XHRlZHNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjInLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRlZHMgICAgICAgICA6IGVkc09iaixcblx0XHR9KTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgaW5zdHJ1bWVudGF0aW9uLmpzb24gZmlsZSAodjI6IGFkZHMgdGhlIGNyZWF0aW9uR3JhcGgga2V5IHdoZW5cblx0ICogdGhlIGNhbGxlciBwYXNzZXMgY3JlYXRpb24tZ3JhcGggZGF0YSDigJQgdGhlIENMSSBhbHdheXMgZG9lcylcblx0ICovXG5cdHdyaXRlSW5zdHJ1bWVudGF0aW9uRmlsZSAocG9pbnRzOiBJbnN0cnVtZW50YXRpb25Qb2ludFtdLCBjcmVhdGlvbkdyYXBoPzogQ3JlYXRpb25HcmFwaCk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2luc3RydW1lbnRhdGlvbi5qc29uJyk7XG5cblx0XHRjb25zdCBqc29uOiBJbnN0cnVtZW50YXRpb25Kc29uID0ge1xuXHRcdFx0dmVyc2lvbiAgICAgOiAyLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRwb2ludHMsXG5cdFx0fTtcblx0XHRpZiAoY3JlYXRpb25HcmFwaCkge1xuXHRcdFx0anNvbi5jcmVhdGlvbkdyYXBoID0gY3JlYXRpb25HcmFwaDtcblx0XHR9XG5cblx0XHRjb25zdCByZWxhdGl2aXplZCA9IHRoaXMucmVsYXRpdml6ZShqc29uKTtcblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShyZWxhdGl2aXplZCwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSBjb250cm9sLmpzb24gZmlsZSAobGV0aGUgY29udHJhY3QsIGZvcm1hdCAxLjIpOiBgY2FsbGVyc2AgaXMgdGhlXG5cdCAqIGNyZWF0aW9uIGdyYXBoIGluc3RydW1lbnRhdGlvbi5qc29uIHYyIGNhcnJpZXMsIGBwb2ludHNgIHRoZSBzYW1lXG5cdCAqIHBsdWdpbi1zdXBwbGllZCBpbnN0cnVtZW50YXRpb24gcG9pbnRzLiBpbnN0cnVtZW50YXRpb24uanNvbiBrZWVwcyBpdHNcblx0ICogc2hhcGUgZm9yIG1uZW1vZ3JhcGhpY2E7IGNvbnRyb2wuanNvbiBpcyB0aGUgY3Jvc3MtbGFuZ3VhZ2UgY29udHJhY3Rcblx0ICogcmVuZGVyaW5nIG9mIHRoZSBzYW1lIGRhdGEuXG5cdCAqL1xuXHR3cml0ZUNvbnRyb2xGaWxlIChwb2ludHM6IEluc3RydW1lbnRhdGlvblBvaW50W10sIGNhbGxlcnM6IENyZWF0aW9uR3JhcGgpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdjb250cm9sLmpzb24nKTtcblxuXHRcdGNvbnN0IGpzb246IENvbnRyb2xKc29uID0ge1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4yJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0Y2FsbGVycyxcblx0XHRcdHBvaW50cyxcblx0XHR9O1xuXG5cdFx0Y29uc3QgcmVsYXRpdml6ZWQgPSB0aGlzLnJlbGF0aXZpemUoanNvbik7XG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkocmVsYXRpdml6ZWQsIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgZmxvdy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlRmxvd0ZpbGUgKGZsb3c6IE1hcDxzdHJpbmcsIEZsb3dJbmZvW10+KTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnZmxvdy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBmbG93T2JqOiBSZWNvcmQ8c3RyaW5nLCBGbG93SW5mb1tdPiA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgZmxvdykge1xuXHRcdFx0Zmxvd09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uOiBGbG93SnNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjInLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRmbG93ICAgICAgICA6IGZsb3dPYmosXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIG1vZHVsZXMuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZU1vZHVsZXNGaWxlIChncmFwaDogTW9kdWxlR3JhcGgpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdtb2R1bGVzLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwIHRvIHBsYWluIG9iamVjdFxuXHRcdGNvbnN0IG1vZHVsZXNPYmo6IE1vZHVsZXNKc29uWyAnbW9kdWxlcycgXSA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgZ3JhcGgubW9kdWxlcykge1xuXHRcdFx0bW9kdWxlc09ialsga2V5IF0gPSB2YWx1ZTtcblx0XHR9XG5cblx0XHRjb25zdCBqc29uOiBNb2R1bGVzSnNvbiA9IHRoaXMucmVsYXRpdml6ZSh7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRtb2R1bGVzICAgICA6IG1vZHVsZXNPYmosXG5cdFx0XHRlZGdlcyAgICAgICA6IGdyYXBoLmVkZ2VzLFxuXHRcdFx0Y3ljbGVzICAgICAgOiBncmFwaC5jeWNsZXMsXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIHNjb3Blcy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlU2NvcGVzRmlsZSAoYW5hbHlzaXM6IFNjb3BlQW5hbHlzaXMpOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdzY29wZXMuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXBzIHRvIHBsYWluIHNoYXBlc1xuXHRcdGNvbnN0IHNjb3Blc09iajogU2NvcGVzSnNvblsgJ3Njb3BlcycgXSA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgYW5hbHlzaXMuc2NvcGVzKSB7XG5cdFx0XHRzY29wZXNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXHRcdGNvbnN0IHZhcmlhYmxlcyA9IEFycmF5LmZyb20oYW5hbHlzaXMudmFyaWFibGVzLnZhbHVlcygpKTtcblxuXHRcdGNvbnN0IGpzb246IFNjb3Blc0pzb24gPSB0aGlzLnJlbGF0aXZpemUoe1xuXHRcdFx0dmVyc2lvbiAgICAgOiAnMS4wJyxcblx0XHRcdGdlbmVyYXRlZEF0IDogbmV3IERhdGUoKS50b0lTT1N0cmluZygpLFxuXHRcdFx0c2NvcGVzICAgICAgOiBzY29wZXNPYmosXG5cdFx0XHR2YXJpYWJsZXMsXG5cdFx0fSk7XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGhpZXJhcmNoeS5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlSGllcmFyY2h5RmlsZSAocm9vdHM6IEhpZXJhcmNoeU5vZGVbXSk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2hpZXJhcmNoeS5qc29uJyk7XG5cblx0XHRjb25zdCBqc29uOiBIaWVyYXJjaHlKc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMicsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdHJvb3RzLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB0aGUgY29sbGVjdGlvbiBtYW5pZmVzdDogb25lIGVudHJ5IHBlciBjb2xsZWN0aW9uIChkZWZhdWx0XG5cdCAqIGZpcnN0IHdoZW4gZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzIGV4aXN0KSwgaWRzICsgZGlzcGxheSBuYW1lcyArXG5cdCAqIGNhbGwgc2l0ZXMgKyBsYW5ndWFnZS4gVGhlIGBjb2xsZWN0aW9uSWQ6OmAgcHJlZml4IG9uIGdyYXBoLW91dHB1dFxuXHQgKiBmdWxsUGF0aHMgam9pbnMgdG8gdGhlIGVudHJ5IGBpZGAuIEZvcm1hdCAxLjI6IHRoZSByZWdpc3RyeVxuXHQgKiBpbnRlcmZhY2UgaXMgbm90IHBhcnQgb2YgdGhlIG1hbmlmZXN0IOKAlCB0aGUgcmVnaXN0cnktcHJlZml4ZWRcblx0ICogYWxpYXNlcyBpbiB0eXBlcy50cyAvIHJlZ2lzdHJ5LnRzIGNvbWUgZnJvbSB0aGUgaW4tbWVtb3J5XG5cdCAqIFR5cGVOb2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSBpbnN0ZWFkLlxuXHQgKi9cblx0d3JpdGVDb2xsZWN0aW9uc0ZpbGUgKGNvbGxlY3Rpb25zOiBDb2xsZWN0aW9uTWFuaWZlc3RFbnRyeVtdKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnY29sbGVjdGlvbnMuanNvbicpO1xuXG5cdFx0Y29uc3QganNvbjogQ29sbGVjdGlvbnNKc29uID0gdGhpcy5yZWxhdGl2aXplKHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMicsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdGNvbGxlY3Rpb25zLFxuXHRcdH0pO1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxufVxuIl19