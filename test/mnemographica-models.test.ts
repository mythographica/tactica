'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as path from 'path';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { TypeGraphImpl } from '../src/graph';
import { TypesGenerator } from '../src/generator';
import { TypesWriter } from '../src/writer';

describe('Mnemographica Models - Real Filesystem Test', () => {
	const fixturesDir = path.join(__dirname, 'fixtures', 'mnemographica-models');
	const outputDir = path.join(__dirname, '..', '.tactica-test-output');
	
	beforeEach(() => {
		// Clean up any previous test output
		if (fs.existsSync(outputDir)) {
			fs.rmSync(outputDir, { recursive: true });
		}
	});
	
	afterEach(() => {
		// Clean up test output after each test
		if (fs.existsSync(outputDir)) {
			fs.rmSync(outputDir, { recursive: true });
		}
	});

	/**
	 * Helper function to analyze a single file and build graph
	 */
	function analyzeFile(fileName: string) {
		const analyzer = new MnemonicaAnalyzer();
		const graph = new TypeGraphImpl();
		
		const filePath = path.join(fixturesDir, fileName);
		const content = fs.readFileSync(filePath, 'utf-8');
		const result = analyzer.analyzeSource(content, filePath);
		
		// Build graph from results - first pass: create all nodes
		const nodeMap = new Map<string, ReturnType<typeof TypeGraphImpl.createNode>>();
		for (const type of result.types) {
			const node = TypeGraphImpl.createNode(
				type.name,
				undefined, // Will set parent in second pass
				type.sourceFile,
				type.line,
				type.column
			);
			for (const [propName, propInfo] of type.properties) {
				node.properties.set(propName, propInfo);
			}
			nodeMap.set(type.name, node);
		}
		
		// Second pass: set up parent-child relationships
		for (const type of result.types) {
			const node = nodeMap.get(type.name)!;
			if (type.parent) {
				const parentNode = nodeMap.get(type.parent.name);
				if (parentNode) {
					node.parent = parentNode;
					parentNode.children.set(node.name, node);
					graph.addChild(parentNode, node);
				}
			} else {
				graph.addRoot(node);
			}
		}
		
		return { analyzer, graph, result };
	}

	/**
	 * Helper function to generate types and write to filesystem
	 */
	function generateAndWrite(graph: TypeGraphImpl) {
		const generator = new TypesGenerator(graph);
		const generated = generator.generateTypesFile();
		
		const writer = new TypesWriter(outputDir);
		writer.write(generated);
		
		const typesPath = path.join(outputDir, 'types.ts');
		expect(fs.existsSync(typesPath)).to.be.true;
		
		return fs.readFileSync(typesPath, 'utf-8');
	}

	it('should generate correct types for Definition/Link pattern with Link: undefined', () => {
		const { graph } = analyzeFile('Definition.ts');
		const typesContent = generateAndWrite(graph);
		
		// Verify ProtoFlat is imported
		expect(typesContent).to.include("import type { ProtoFlat } from 'mnemonica'");
		
		// DefinitionInstance (root type) should have Link constructor property
		expect(typesContent).to.include('export type DefinitionInstance = {');
		expect(typesContent).to.include('Link: TypeConstructor<LinkInstance>');
		
		// LinkInstance (nested type) should have Link: undefined
		expect(typesContent).to.include('export type LinkInstance = ProtoFlat<DefinitionInstance, {');
		expect(typesContent).to.include('Link: undefined;');
	});

	it('should generate correct types for Scene2D/Camera2D/GraphNode2D pattern', () => {
		const { graph } = analyzeFile('Scene2D.ts');
		const typesContent = generateAndWrite(graph);
		
		// Scene2DInstance (root) should have Camera2D and GraphNode2D constructors
		expect(typesContent).to.include('export type Scene2DInstance = {');
		expect(typesContent).to.include('Camera2D: TypeConstructor<Camera2DInstance>');
		expect(typesContent).to.include('GraphNode2D: TypeConstructor<GraphNode2DInstance>');
		
		// Camera2DInstance (nested) should have Camera2D: undefined
		expect(typesContent).to.include('export type Camera2DInstance = ProtoFlat<Scene2DInstance, {');
		expect(typesContent).to.include('Camera2D: undefined;');
		
		// GraphNode2DInstance (nested) should have GraphNode2D: undefined
		// Note: Nested type instances don't get children constructors, only root types do
		expect(typesContent).to.include('export type GraphNode2DInstance = ProtoFlat<Scene2DInstance, {');
		expect(typesContent).to.include('GraphNode2D: undefined;');
		
		// Deeply nested types should also have Subtype: undefined and proper ProtoFlat chain
		expect(typesContent).to.include('export type Link2DInstance = ProtoFlat<GraphNode2DInstance, {');
		expect(typesContent).to.include('Link2D: undefined;');
		
		expect(typesContent).to.include('export type Tooltip2DInstance = ProtoFlat<GraphNode2DInstance, {');
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
		
		// UsageEntryInstance should have UsageEntry: undefined
		expect(typesContent).to.include('export type UsageEntryInstance = ProtoFlat<UsagesInstance, {');
		expect(typesContent).to.include('UsageEntry: undefined;');
	});

	it('should generate correct types for Scene3D pattern', () => {
		const { graph } = analyzeFile('Scene3D.ts');
		const typesContent = generateAndWrite(graph);
		
		// Scene3DInstance (root) should have Camera3D and GraphNode3D
		expect(typesContent).to.include('export type Scene3DInstance = {');
		expect(typesContent).to.include('Camera3D: TypeConstructor<Camera3DInstance>');
		expect(typesContent).to.include('GraphNode3D: TypeConstructor<GraphNode3DInstance>');
		
		// Camera3DInstance should have Camera3D: undefined
		expect(typesContent).to.include('export type Camera3DInstance = ProtoFlat<Scene3DInstance, {');
		expect(typesContent).to.include('Camera3D: undefined;');
		
		// GraphNode3DInstance should have GraphNode3D: undefined
		expect(typesContent).to.include('GraphNode3D: undefined;');
		
		// Deeply nested types should also have Subtype: undefined
		expect(typesContent).to.include('export type Link3DInstance = ProtoFlat<GraphNode3DInstance, {');
		expect(typesContent).to.include('Link3D: undefined;');
		expect(typesContent).to.include('export type Tooltip3DInstance = ProtoFlat<GraphNode3DInstance, {');
		expect(typesContent).to.include('Tooltip3D: undefined;');
	});

	it('should generate correct types for Trie pattern', () => {
		const { graph } = analyzeFile('Trie.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type TrieInstance = {');
		expect(typesContent).to.include('GraphNodeTrie: TypeConstructor<GraphNodeTrieInstance>');
		
		expect(typesContent).to.include('export type GraphNodeTrieInstance = ProtoFlat<TrieInstance, {');
		expect(typesContent).to.include('GraphNodeTrie: undefined;');
		
		// Deeply nested types should also have Subtype: undefined
		expect(typesContent).to.include('export type LinkTrieInstance = ProtoFlat<GraphNodeTrieInstance, {');
		expect(typesContent).to.include('LinkTrie: undefined;');
		expect(typesContent).to.include('export type ContextMenuInstance = ProtoFlat<GraphNodeTrieInstance, {');
		expect(typesContent).to.include('ContextMenu: undefined;');
	});

	it('should generate correct types for Types pattern', () => {
		const { graph } = analyzeFile('Types.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type TypesInstance = {');
		expect(typesContent).to.include('TypeEntry: TypeConstructor<TypeEntryInstance>');
		
		expect(typesContent).to.include('export type TypeEntryInstance = ProtoFlat<TypesInstance, {');
		expect(typesContent).to.include('TypeEntry: undefined;');
	});

	it('should generate correct types for Registry pattern', () => {
		const { graph } = analyzeFile('Registry.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type RegistryInstance = {');
		expect(typesContent).to.include('DefinitionEntry: TypeConstructor<DefinitionEntryInstance>');
		
		expect(typesContent).to.include('export type DefinitionEntryInstance = ProtoFlat<RegistryInstance, {');
		expect(typesContent).to.include('DefinitionEntry: undefined;');
	});

	it('should generate correct types for LoggerTab pattern', () => {
		const { graph } = analyzeFile('LoggerTab.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type LoggerTabInstance = {');
		expect(typesContent).to.include('LogEntry: TypeConstructor<LogEntryInstance>');
		
		expect(typesContent).to.include('export type LogEntryInstance = ProtoFlat<LoggerTabInstance, {');
		expect(typesContent).to.include('LogEntry: undefined;');
	});

	it('should generate correct types for Main/Adapter pattern', () => {
		const { graph } = analyzeFile('Main.ts');
		const typesContent = generateAndWrite(graph);
		
		expect(typesContent).to.include('export type MainInstance = {');
		expect(typesContent).to.include('Adapter: TypeConstructor<AdapterInstance>');
		
		expect(typesContent).to.include('export type AdapterInstance = ProtoFlat<MainInstance, {');
		expect(typesContent).to.include('Adapter: undefined;');
	});
});
