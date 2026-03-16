'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as path from 'path';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { TypeGraphImpl } from '../src/graph';
import { TypesGenerator } from '../src/generator';
import { TypesWriter } from '../src/writer';

const fixturesDir = path.join(__dirname, 'fixtures', 'mnemographica-models');
const testOutputDir = path.join(__dirname, '.test-mnemographica');

describe('Mnemographica Models - Real Filesystem Test', () => {
	beforeEach(() => {
		if (fs.existsSync(testOutputDir)) {
			fs.rmSync(testOutputDir, { recursive: true });
		}
		fs.mkdirSync(testOutputDir, { recursive: true });
	});

	afterEach(() => {
		if (fs.existsSync(testOutputDir)) {
			fs.rmSync(testOutputDir, { recursive: true });
		}
	});

	function analyzeFile(fileName: string) {
		const filePath = path.join(fixturesDir, fileName);
		const content = fs.readFileSync(filePath, 'utf-8');
		
		const analyzer = new MnemonicaAnalyzer();
		const result = analyzer.analyzeSource(content, filePath);
		const graph = analyzer.getGraph();
		
		return { analyzer, graph, result };
	}

	function generateAndWrite(graph: TypeGraphImpl): string {
		const generator = new TypesGenerator(graph);
		const generated = generator.generateTypesFile();
		
		const writer = new TypesWriter(testOutputDir);
		writer.writeTypesFile(generated);
		
		return generated.content;
	}

	it('should generate correct types for Definition/Link pattern with Link: undefined', () => {
		const { graph } = analyzeFile('Definition.ts');
		const typesContent = generateAndWrite(graph);
		
		// Verify ProtoFlat is imported
		expect(typesContent).to.include("import type { ProtoFlat } from 'mnemonica'");
		
		// Definition (root type) should have Link constructor property
		expect(typesContent).to.include('export type Definition = {');
		expect(typesContent).to.include('Link:');
		expect(typesContent).to.include('Definition_Link');
		
		// Definition_Link (nested type) should have Link: undefined
		expect(typesContent).to.include('export type Definition_Link = ProtoFlat<Definition, {');
		expect(typesContent).to.include('Link: undefined;');
	});

	it('should generate correct types for Scene2D/Camera2D/GraphNode2D pattern', () => {
		const { graph } = analyzeFile('Scene2D.ts');
		const typesContent = generateAndWrite(graph);
		
		// Scene2D (root) should have Camera2D and GraphNode2D constructors
		expect(typesContent).to.include('export type Scene2D = {');
		expect(typesContent).to.include('Camera2D:');
		expect(typesContent).to.include('Scene2D_Camera2D');
		expect(typesContent).to.include('GraphNode2D:');
		expect(typesContent).to.include('Scene2D_GraphNode2D');
		
		// Scene2D_Camera2D (nested) should have Camera2D: undefined
		expect(typesContent).to.include('export type Scene2D_Camera2D = ProtoFlat<Scene2D, {');
		expect(typesContent).to.include('Camera2D: undefined;');
		
		// Scene2D_GraphNode2D (nested) should have GraphNode2D: undefined
		// Note: Nested type instances don't get children constructors, only root types do
		expect(typesContent).to.include('export type Scene2D_GraphNode2D = ProtoFlat<Scene2D, {');
		expect(typesContent).to.include('GraphNode2D: undefined;');
		
		// Deeply nested types should also have Subtype: undefined and proper ProtoFlat chain
		expect(typesContent).to.include('export type Scene2D_GraphNode2D_Link2D = ProtoFlat<Scene2D_GraphNode2D, {');
		expect(typesContent).to.include('Link2D: undefined;');
		
		expect(typesContent).to.include('export type Scene2D_GraphNode2D_Tooltip2D = ProtoFlat<Scene2D_GraphNode2D, {');
		expect(typesContent).to.include('Tooltip2D: undefined;');
	});

	it('should extract class methods from Usages class (has, set, values, size getter)', () => {
		const { analyzer, graph, result } = analyzeFile('Usages.ts');
		const typesContent = generateAndWrite(graph);
		
		// Find Usages type
		const usagesType = result.types.find(t => t.name === 'Usages');
		expect(usagesType).to.exist;
		
		// Should have createdAt property
		expect(usagesType!.properties.has('createdAt')).to.be.true;
		
		// Should have class methods: has, set, values
		expect(usagesType!.properties.has('has')).to.be.true;
		expect(usagesType!.properties.has('set')).to.be.true;
		expect(usagesType!.properties.has('values')).to.be.true;
		
		// Should have getter: size
		expect(usagesType!.properties.has('size')).to.be.true;
		
		// Verify methods are in generated content
		expect(typesContent).to.include('has:');
		expect(typesContent).to.include('set:');
		expect(typesContent).to.include('values:');
		expect(typesContent).to.include('size:');
		
		// Usages_UsageEntry should have UsageEntry: undefined
		expect(typesContent).to.include('export type Usages_UsageEntry = ProtoFlat<Usages, {');
		expect(typesContent).to.include('UsageEntry: undefined;');
	});

	it('should generate correct types for Scene3D pattern', () => {
		const { graph } = analyzeFile('Scene3D.ts');
		const typesContent = generateAndWrite(graph);
		
		// Scene3D (root) should have Camera3D and GraphNode3D
		expect(typesContent).to.include('export type Scene3D = {');
		expect(typesContent).to.include('Camera3D:');
		expect(typesContent).to.include('Scene3D_Camera3D');
		expect(typesContent).to.include('GraphNode3D:');
		expect(typesContent).to.include('Scene3D_GraphNode3D');
		
		// Scene3D_Camera3D should have Camera3D: undefined
		expect(typesContent).to.include('export type Scene3D_Camera3D = ProtoFlat<Scene3D, {');
		expect(typesContent).to.include('Camera3D: undefined;');
		
		// Scene3D_GraphNode3D should have GraphNode3D: undefined
		expect(typesContent).to.include('GraphNode3D: undefined;');
		
		// Deeply nested types should also have Subtype: undefined
		expect(typesContent).to.include('export type Scene3D_GraphNode3D_Link3D = ProtoFlat<Scene3D_GraphNode3D, {');
		expect(typesContent).to.include('Link3D: undefined;');
		expect(typesContent).to.include('export type Scene3D_GraphNode3D_Tooltip3D = ProtoFlat<Scene3D_GraphNode3D, {');
		expect(typesContent).to.include('Tooltip3D: undefined;');
	});

	it('should generate correct types for Trie pattern', () => {
		const { graph } = analyzeFile('Trie.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type Trie = {');
		expect(typesContent).to.include('GraphNodeTrie:');
		expect(typesContent).to.include('Trie_GraphNodeTrie');
		
		expect(typesContent).to.include('export type Trie_GraphNodeTrie = ProtoFlat<Trie, {');
		expect(typesContent).to.include('GraphNodeTrie: undefined;');
		
		// Deeply nested types should also have Subtype: undefined
		expect(typesContent).to.include('export type Trie_GraphNodeTrie_LinkTrie = ProtoFlat<Trie_GraphNodeTrie, {');
		expect(typesContent).to.include('LinkTrie: undefined;');
		expect(typesContent).to.include('export type Trie_GraphNodeTrie_ContextMenu = ProtoFlat<Trie_GraphNodeTrie, {');
		expect(typesContent).to.include('ContextMenu: undefined;');
	});

	it('should generate correct types for Types pattern', () => {
		const { graph } = analyzeFile('Types.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type Types = {');
		expect(typesContent).to.include('TypeEntry:');
		expect(typesContent).to.include('Types_TypeEntry');
		
		expect(typesContent).to.include('export type Types_TypeEntry = ProtoFlat<Types, {');
		expect(typesContent).to.include('TypeEntry: undefined;');
	});

	it('should generate correct types for Registry pattern', () => {
		const { graph } = analyzeFile('Registry.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type Registry = {');
		expect(typesContent).to.include('DefinitionEntry:');
		expect(typesContent).to.include('Registry_DefinitionEntry');
		
		expect(typesContent).to.include('export type Registry_DefinitionEntry = ProtoFlat<Registry, {');
		expect(typesContent).to.include('DefinitionEntry: undefined;');
	});

	it('should generate correct types for LoggerTab pattern', () => {
		const { graph } = analyzeFile('LoggerTab.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type LoggerTab = {');
		expect(typesContent).to.include('LogEntry:');
		expect(typesContent).to.include('LoggerTab_LogEntry');
		
		expect(typesContent).to.include('export type LoggerTab_LogEntry = ProtoFlat<LoggerTab, {');
		expect(typesContent).to.include('LogEntry: undefined;');
	});

	it('should generate correct types for Main/Adapter pattern', () => {
		const { graph } = analyzeFile('Main.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type Main = {');
		expect(typesContent).to.include('Adapter:');
		expect(typesContent).to.include('Main_Adapter');
		
		expect(typesContent).to.include('export type Main_Adapter = ProtoFlat<Main, {');
		expect(typesContent).to.include('Adapter: undefined;');
	});
});
