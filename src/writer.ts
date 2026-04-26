'use strict';

import * as fs from 'fs';
import * as path from 'path';
import { GeneratedTypes, DefinitionInfo, UsageInfo, DriftReport } from './types';

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
			fs.mkdirSync(this.outputDir, { recursive: true });
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
	 * Write drift.txt — one human-readable line per drift report. Returns
	 * the absolute path written, or null when no reports were given (so
	 * we don't leave stale files around).
	 */
	writeDriftReport (reports: DriftReport[]): string | null {
		if (!reports || reports.length === 0) return null;
		this.ensureDirectory();
		const filePath = path.join(this.outputDir, 'drift.txt');
		const lines = reports.map(r =>
			`${r.fileName}:${r.line} [${r.kind}] ${r.message}`
		);
		fs.writeFileSync(filePath, `${lines.join('\n')}\n`, 'utf-8');
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
}
