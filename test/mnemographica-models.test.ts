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
		
		// Verify LinkInstance has Link: undefined
		expect(typesContent).to.include('Link: undefined');
		
		// Verify the pattern: LinkInstance = ProtoFlat<DefinitionInstance, { ... Link: undefined; }>
		const linkInstanceMatch = typesContent.match(/export type LinkInstance = ProtoFlat<DefinitionInstance, \{[\s\S]*?Link: undefined;[\s\S]*?\}>;/);
		expect(linkInstanceMatch).to.not.be.null;
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
		
		// Camera2DInstance should have Camera2D: undefined and GraphNode2D: undefined
		expect(typesContent).to.include('Camera2D: undefined');
		expect(typesContent).to.include('GraphNode2D: undefined');
		
		// GraphNode2DInstance should have Camera2D: undefined
		const graphNode2dMatch = typesContent.match(/export type GraphNode2DInstance = ProtoFlat<Scene2DInstance, \{[\s\S]*?Camera2D: undefined;[\s\S]*?\}>;/);
		expect(graphNode2dMatch).to.not.be.null;
	});
});
