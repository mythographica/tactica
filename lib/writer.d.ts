import { GeneratedTypes, DefinitionInfo, UsageInfo, EDSInfo, FlowInfo, HierarchyNode, InstrumentationPoint } from './types';
/**
 * Writes generated types to file system
 */
export declare class TypesWriter {
    private outputDir;
    constructor(outputDir?: string);
    /**
     * Legacy write method - delegates to writeTypesFile
     */
    write(generated: GeneratedTypes): string;
    /**
     * Write types.ts file (exportable type aliases - default mode)
     */
    writeTypesFile(generated: GeneratedTypes): string;
    /**
     * Write global augmentation file (index.d.ts - module augmentation mode)
     */
    writeGlobalAugmentation(generated: GeneratedTypes): string;
    /**
     * Write to a custom filename
     */
    writeTo(filename: string, content: string): string;
    /**
     * Ensure output directory exists
     */
    private ensureDirectory;
    /**
     * Clean the output directory
     */
    clean(): void;
    /**
     * Get output directory
     */
    getOutputDir(): string;
    /**
     * Write definitions.json file
     */
    writeDefinitionsFile(definitions: Map<string, DefinitionInfo>): string;
    /**
     * Write usages.json file
     */
    writeUsagesFile(usages: Map<string, UsageInfo[]>): string;
    /**
     * Write eds.json file
     */
    writeEDSFile(eds: Map<string, EDSInfo[]>): string;
    /**
     * Write instrumentation.json file
     */
    writeInstrumentationFile(points: InstrumentationPoint[]): string;
    /**
     * Write flow.json file
     */
    writeFlowFile(flow: Map<string, FlowInfo[]>): string;
    /**
     * Write hierarchy.json file
     */
    writeHierarchyFile(roots: HierarchyNode[]): string;
}
