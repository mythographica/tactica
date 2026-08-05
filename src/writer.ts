'use strict';

import * as fs from 'fs';
import * as path from 'path';
import {
	GeneratedTypes, DefinitionInfo, UsageInfo, EDSInfo, FlowInfo, FlowJson, HierarchyNode, HierarchyJson 
} from './types';

/**
 * Writes generated types to file system
 */
export class TypesWriter {
	private outputDir: string;

	constructor (outputDir = '.tactica') {
		this.outputDir = outputDir;
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
	 * Write definitions.json file
	 */
	writeDefinitionsFile (definitions: Map<string, DefinitionInfo>): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'definitions.json');

		// Convert Map to plain object
		const definitionsObj: Record<string, DefinitionInfo> = {};
		for (const [ key, value ] of definitions) {
			definitionsObj[ key ] = value;
		}

		const json = {
			version     : '1.0',
			generatedAt : new Date().toISOString(),
			definitions : definitionsObj,
		};

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

		const json = {
			version     : '1.0',
			generatedAt : new Date().toISOString(),
			usages      : usagesObj,
		};

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

		const json = {
			version     : '1.0',
			generatedAt : new Date().toISOString(),
			eds         : edsObj,
		};

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
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

		const json: FlowJson = {
			version     : '1.0',
			generatedAt : new Date().toISOString(),
			flow        : flowObj,
		};

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
		return filePath;
	}

	/**
	 * Write hierarchy.json file
	 */
	writeHierarchyFile (roots: HierarchyNode[]): string {
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'hierarchy.json');

		const json: HierarchyJson = {
			version     : '1.0',
			generatedAt : new Date().toISOString(),
			roots,
		};

		fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
		return filePath;
	}
}
