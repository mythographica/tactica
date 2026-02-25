'use strict';

import * as fs from 'fs';
import * as path from 'path';
import { GeneratedTypes } from './types';

/**
 * File writer for generated types
 */
export class TypesWriter {
	private outputDir: string;

	constructor(outputDir = '.tactica') {
		this.outputDir = outputDir;
	}

	/**
	 * Write generated types to file
	 */
	write(generated: GeneratedTypes): string {
		// Ensure output directory exists
		this.ensureDirectory();

		const outputPath = path.join(this.outputDir, 'types.d.ts');

		// Write the file
		fs.writeFileSync(outputPath, generated.content, 'utf-8');

		// Update .gitignore if needed
		this.updateGitignore();

		return outputPath;
	}

	/**
	 * Write types.ts file with complete interfaces
	 */
	writeTypesFile(generated: GeneratedTypes): string {
		this.ensureDirectory();

		const outputPath = path.join(this.outputDir, 'types.ts');
		fs.writeFileSync(outputPath, generated.content, 'utf-8');

		return outputPath;
	}

	/**
		 * Write global augmentation file
		 */
		writeGlobalAugmentation(generated: GeneratedTypes): string {
			this.ensureDirectory();
	
			// Use index.d.ts so TypeScript picks it up automatically from typeRoots
			const outputPath = path.join(this.outputDir, 'index.d.ts');
			fs.writeFileSync(outputPath, generated.content, 'utf-8');
	
			// Update .gitignore if needed
			this.updateGitignore();
	
			return outputPath;
		}

	/**
		* Write types with custom filename
		*/
	writeTo(filename: string, content: string): string {
		this.ensureDirectory();
		const outputPath = path.join(this.outputDir, filename);
		fs.writeFileSync(outputPath, content, 'utf-8');
		return outputPath;
	}

	/**
	 * Ensure output directory exists
	 */
	private ensureDirectory(): void {
		if (!fs.existsSync(this.outputDir)) {
			fs.mkdirSync(this.outputDir, { recursive: true });
		}
	}

	/**
	 * Update .gitignore to exclude .tactica folder
	 */
	private updateGitignore(): void {
		const gitignorePath = path.join(process.cwd(), '.gitignore');

		if (!fs.existsSync(gitignorePath)) {
			// Create .gitignore
			fs.writeFileSync(gitignorePath, `${this.outputDir}/\n`, 'utf-8');
			return;
		}

		const content = fs.readFileSync(gitignorePath, 'utf-8');
		const lines = content.split('\n');

		// Check if already ignored
		const isIgnored = lines.some(line =>
			line.trim() === this.outputDir ||
			line.trim() === `${this.outputDir}/`
		);

		if (!isIgnored) {
			// Add to .gitignore
			const newContent = content.endsWith('\n')
				? `${content}${this.outputDir}/\n`
				: `${content}\n${this.outputDir}/\n`;
			fs.writeFileSync(gitignorePath, newContent, 'utf-8');
		}
	}

	/**
	 * Clean the output directory
	 */
	clean(): void {
		if (fs.existsSync(this.outputDir)) {
			const files = fs.readdirSync(this.outputDir);
			for (const file of files) {
				fs.unlinkSync(path.join(this.outputDir, file));
			}
		}
	}

	/**
	 * Get the output directory path
	 */
	getOutputDir(): string {
		return this.outputDir;
	}
}
