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

	it('should generate correct types for Definition/Link pattern with Link: undefined', () => {
		// Analyze the models directory
		const analyzer = new MnemonicaAnalyzer();
		const graph = new TypeGraphImpl();
		
		// Read and analyze Definition.ts
		const definitionPath = path.join(fixturesDir, 'Definition.ts');
		const definitionContent = fs.readFileSync(definitionPath, 'utf-8');
		const definitionResult = analyzer.analyzeSource(definitionContent, definitionPath);
		
		// Build graph from results - first pass: create all nodes
		const nodeMap = new Map<string, ReturnType<typeof TypeGraphImpl.createNode>>();
		for (const type of definitionResult.types) {
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
		for (const type of definitionResult.types) {
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
		
		// Generate types
		const generator = new TypesGenerator(graph);
		const generated = generator.generateTypesFile();
		
		// Write to actual filesystem
		const writer = new TypesWriter(outputDir);
		writer.write(generated);
		
		// Read the actual generated file from disk
		const typesPath = path.join(outputDir, 'types.ts');
		expect(fs.existsSync(typesPath)).to.be.true;
		
		const typesContent = fs.readFileSync(typesPath, 'utf-8');
		
		// Verify ProtoFlat is imported
		expect(typesContent).to.include("import type { ProtoFlat } from 'mnemonica'");
		
		// LinkInstance should NOT have Link: undefined - subtype constructors are accessible via parent only
		// The type only contains the properties defined in the constructor
		expect(typesContent).to.include('export type LinkInstance = ProtoFlat<DefinitionInstance, {');
		// Verify LinkInstance does NOT contain "Link: undefined" (this was a bug)
		const linkInstanceMatch = typesContent.match(/export type LinkInstance = ProtoFlat<DefinitionInstance, \{[^}]*Link: undefined;/);
		expect(linkInstanceMatch).to.be.null;
	});

	it('should generate correct types for Scene2D/Camera2D/GraphNode2D pattern with sibling undefineds', () => {
		// Analyze the Scene2D model
		const analyzer = new MnemonicaAnalyzer();
		const graph = new TypeGraphImpl();
		
		const scene2dPath = path.join(fixturesDir, 'Scene2D.ts');
		const scene2dContent = fs.readFileSync(scene2dPath, 'utf-8');
		const result = analyzer.analyzeSource(scene2dContent, scene2dPath);
		
		// Build graph - first pass: create all nodes
		const nodeMap = new Map<string, ReturnType<typeof TypeGraphImpl.createNode>>();
		for (const type of result.types) {
			const node = TypeGraphImpl.createNode(
				type.name,
				undefined,
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
		
		// Generate types
		const generator = new TypesGenerator(graph);
		const generated = generator.generateTypesFile();
		
		// Write to filesystem
		const writer = new TypesWriter(outputDir);
		writer.write(generated);
		
		// Read and verify
		const typesPath = path.join(outputDir, 'types.ts');
		const typesContent = fs.readFileSync(typesPath, 'utf-8');
		
		// Camera2DInstance should NOT have Camera2D: undefined or GraphNode2D: undefined
		// These subtype constructors are accessible via parent only
		expect(typesContent).to.include('export type Camera2DInstance = ProtoFlat<Scene2DInstance, {');
		// Verify Camera2DInstance does NOT contain "Camera2D: undefined" (this was a bug)
		const camera2dMatch = typesContent.match(/export type Camera2DInstance = ProtoFlat<Scene2DInstance, \{[^}]*Camera2D: undefined;/);
		expect(camera2dMatch).to.be.null;

		// GraphNode2DInstance should NOT have Camera2D: undefined either
		const graphNode2dMatch = typesContent.match(/export type GraphNode2DInstance = ProtoFlat<Scene2DInstance, \{[^}]*Camera2D: undefined;/);
		expect(graphNode2dMatch).to.be.null;
	});

	// Note: Full Usages/UsageEntry test requires type alias resolution
	// which needs additional implementation to collect and resolve type aliases
});
