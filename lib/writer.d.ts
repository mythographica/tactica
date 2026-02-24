import { GeneratedTypes } from './types';
/**
 * File writer for generated types
 */
export declare class TypesWriter {
    private outputDir;
    constructor(outputDir?: string);
    /**
     * Write generated types to file
     */
    write(generated: GeneratedTypes): string;
    /**
     * Write types with custom filename
     */
    writeTo(filename: string, content: string): string;
    /**
     * Ensure output directory exists
     */
    private ensureDirectory;
    /**
     * Update .gitignore to exclude .mnemonica folder
     */
    private updateGitignore;
    /**
     * Clean the output directory
     */
    clean(): void;
    /**
     * Get the output directory path
     */
    getOutputDir(): string;
}
