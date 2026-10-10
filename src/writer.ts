'use strict';

import * as fs from 'fs';
import * as path from 'path';
import {
	GeneratedTypes, DefinitionInfo, UsageInfo, EDSInfo, FlowInfo, FlowJson, HierarchyNode, HierarchyJson,
	InstrumentationPoint, InstrumentationJson, ModuleGraph, ModulesJson, ScopeAnalysis, ScopesJson, CreationGraph,
	CollectionManifestEntry, CollectionsJson, ControlJson, TypeGraph, DefinitionField, DefinitionArg
} from './types';

/**
 * Writes generated types to file system
 */
export class TypesWriter {
	private outputDir: string;
	private projectRoot?: string;

	constructor (outputDir = '.tactica', projectRoot?: string) {
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
	private relativize<T> (payload: T): T {
		if (this.projectRoot === undefined) {
			return payload;
		}
		const prefix = this.projectRoot + path.sep;
		const walk = (input: unknown): unknown => {
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
				const walked: Record<string, unknown> = {};
				for (const [ key, value ] of Object.entries(input)) {
					const walkedKey = walk(key) as string;
					walked[ walkedKey ] = walk(value);
				}
				return walked;
			}
			return input;
		};
		const result = walk(payload);
		return result as T;
	}

	/**
	 * Legacy write method - delegates to writeTypesFile
	 */
	write (generated: GeneratedTypes): string {
		return this.writeTypesFile(generated);
	}

	/**
	 * Write types.ts file (exportable type aliases - default mode)
	 */
	writeTypesFile (generated: GeneratedTypes): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'types.ts');
		fs.writeFileSync(filePath, generated.content, 'utf-8');
		return filePath;
	}

	/**
	 * Write global augmentation file (index.d.ts - module augmentation mode)
	 */
	writeGlobalAugmentation (generated: GeneratedTypes): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'index.d.ts');
		fs.writeFileSync(filePath, generated.content, 'utf-8');
		return filePath;
	}

	/**
	 * Write to a custom filename
	 */
	writeTo (filename: string, content: string): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, filename);
		fs.writeFileSync(filePath, content, 'utf-8');
		return filePath;
	}

	/**
	 * Ensure output directory exists
	 */
	private ensureDirectory (): void {
		if (!fs.existsSync(this.outputDir)) {
			fs.mkdirSync(this.outputDir, { recursive : true });
		}
	}

	/**
	 * Clean the output directory
	 */
	clean (): void {
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
	getOutputDir (): string {
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
	writeDefinitionsFile (definitions: Map<string, DefinitionInfo>, graph?: TypeGraph): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'definitions.json');

		// Convert Map to plain object
		const definitionsObj: Record<string, DefinitionInfo> = {};
		for (const [ key, value ] of definitions) {
			definitionsObj[ key ] = value;
		}

		if (graph) {
			for (const [ key, value ] of definitions) {
				const node = graph.findType(key);
				if (!node) {
					continue;
				}
				// enrich a copy — the analyzer's definitions map stays untouched
				const entry: DefinitionInfo = { ...value };
				const fields: DefinitionField[] = [];
				for (const propInfo of node.properties.values()) {
					fields.push({
						name     : propInfo.name,
						type     : propInfo.type,
						optional : propInfo.optional
					});
				}
				entry.fields = fields;
				if (node.constructorParams !== undefined) {
					const args: DefinitionArg[] = node.constructorParams.map((param) => {
						// a rest parameter may always receive nothing:
						// the contract gives it `kind` and no `optional`
						const arg: DefinitionArg = param.kind === 'rest'
							? {
								name : param.name,
								type : param.type,
								kind : 'rest'
							}
							: {
								name     : param.name,
								type     : param.type,
								optional : param.optional
							};
						return arg;
					});
					entry.args = args;
				}
				definitionsObj[ key ] = entry;
			}
		}

		const json = this.relativize({
			version     : '1.1',
			generatedAt : new Date().toISOString(),
			definitions : definitionsObj,
		});

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
		return filePath;
	}

	/**
	 * Write usages.json file
	 */
	writeUsagesFile (usages: Map<string, UsageInfo[]>): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'usages.json');

		// Convert Map to plain object
		const usagesObj: Record<string, UsageInfo[]> = {};
		for (const [ key, value ] of usages) {
			usagesObj[ key ] = value;
		}

		const json = this.relativize({
			version     : '1.1',
			generatedAt : new Date().toISOString(),
			usages      : usagesObj,
		});

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
		return filePath;
	}

	/**
	 * Write eds.json file
	 */
	writeEDSFile (eds: Map<string, EDSInfo[]>): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'eds.json');

		// Convert Map to plain object
		const edsObj: Record<string, EDSInfo[]> = {};
		for (const [ key, value ] of eds) {
			edsObj[ key ] = value;
		}

		const json = this.relativize({
			version     : '1.1',
			generatedAt : new Date().toISOString(),
			eds         : edsObj,
		});

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
		return filePath;
	}

	/**
	 * Write instrumentation.json file (v2: adds the creationGraph key when
	 * the caller passes creation-graph data — the CLI always does)
	 */
	writeInstrumentationFile (points: InstrumentationPoint[], creationGraph?: CreationGraph): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'instrumentation.json');

		const json: InstrumentationJson = {
			version     : 2,
			generatedAt : new Date().toISOString(),
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
	writeControlFile (points: InstrumentationPoint[], callers: CreationGraph): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'control.json');

		const json: ControlJson = {
			version     : '1.1',
			generatedAt : new Date().toISOString(),
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
	writeFlowFile (flow: Map<string, FlowInfo[]>): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'flow.json');

		// Convert Map to plain object
		const flowObj: Record<string, FlowInfo[]> = {};
		for (const [ key, value ] of flow) {
			flowObj[ key ] = value;
		}

		const json: FlowJson = this.relativize({
			version     : '1.1',
			generatedAt : new Date().toISOString(),
			flow        : flowObj,
		});

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
		return filePath;
	}

	/**
	 * Write modules.json file
	 */
	writeModulesFile (graph: ModuleGraph): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'modules.json');

		// Convert Map to plain object
		const modulesObj: ModulesJson[ 'modules' ] = {};
		for (const [ key, value ] of graph.modules) {
			modulesObj[ key ] = value;
		}

		const json: ModulesJson = this.relativize({
			version     : '1.0',
			generatedAt : new Date().toISOString(),
			modules     : modulesObj,
			edges       : graph.edges,
			cycles      : graph.cycles,
		});

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
		return filePath;
	}

	/**
	 * Write scopes.json file
	 */
	writeScopesFile (analysis: ScopeAnalysis): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'scopes.json');

		// Convert Maps to plain shapes
		const scopesObj: ScopesJson[ 'scopes' ] = {};
		for (const [ key, value ] of analysis.scopes) {
			scopesObj[ key ] = value;
		}
		const variables = Array.from(analysis.variables.values());

		const json: ScopesJson = this.relativize({
			version     : '1.0',
			generatedAt : new Date().toISOString(),
			scopes      : scopesObj,
			variables,
		});

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
		return filePath;
	}

	/**
	 * Write hierarchy.json file
	 */
	writeHierarchyFile (roots: HierarchyNode[]): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'hierarchy.json');

		const json: HierarchyJson = this.relativize({
			version     : '1.1',
			generatedAt : new Date().toISOString(),
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
	writeCollectionsFile (collections: CollectionManifestEntry[]): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'collections.json');

		const json: CollectionsJson = this.relativize({
			version     : '1.1',
			generatedAt : new Date().toISOString(),
			collections,
		});

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
		return filePath;
	}
}
