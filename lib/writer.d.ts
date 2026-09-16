import { GeneratedTypes, DefinitionInfo, UsageInfo, EDSInfo, FlowInfo, HierarchyNode, InstrumentationPoint, ModuleGraph, ScopeAnalysis, CreationGraph } from './types';
/**
 * Writes generated types to file system
 */
export declare class TypesWriter {
    private outputDir;
    private projectRoot?;
    constructor(outputDir?: string, projectRoot?: string);
    /**
     * Rewrite every project-rooted absolute path in the payload to a
     * project-relative one (values AND object keys), so .tactica output
     * stays portable across machines and checkouts. Paths outside the
     * project root keep their absolute form — they genuinely are
     * machine-specific. Consumers resolve relative entries against the
     * directory that holds .tactica.
     */
    private relativize;
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
     * Write instrumentation.json file (v2: adds the creationGraph key when
     * the caller passes creation-graph data — the CLI always does)
     */
    writeInstrumentationFile(points: InstrumentationPoint[], creationGraph?: CreationGraph): string;
    /**
     * Write flow.json file
     */
    writeFlowFile(flow: Map<string, FlowInfo[]>): string;
    /**
     * Write modules.json file
     */
    writeModulesFile(graph: ModuleGraph): string;
    /**
     * Write scopes.json file
     */
    writeScopesFile(analysis: ScopeAnalysis): string;
    /**
     * Write hierarchy.json file
     */
    writeHierarchyFile(roots: HierarchyNode[]): string;
}
