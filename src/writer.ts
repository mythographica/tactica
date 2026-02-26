'use strict';

import * as fs from 'fs';
import * as path from 'path';
import { GeneratedTypes } from './types';

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
}
