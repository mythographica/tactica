
/// <reference types="node" />
/// <reference types="mocha" />
/// <reference types="chai" />
'use strict';

import { expect } from 'chai';
import * as path from 'path';
import { TopologicaAnalyzer } from '../src/topologica-analyzer';
import { TypeGraphImpl } from '../src/graph';

describe('TopologicaAnalyzer', () => {
	let analyzer: TopologicaAnalyzer;

	beforeEach(() => {
		analyzer = new TopologicaAnalyzer();
	});

	describe('TypeScript directory structures', () => {
		it('should analyze ai-topology fixture with .ts files', () => {
			const fixturePath = path.join(__dirname, 'fixtures', 'ai-topology');
			const result = analyzer.analyzeDirectory(fixturePath);

			expect(result.errors).to.have.length(0);
			expect(result.types.size).to.be.greaterThan(0);

			// Check root type
			expect(result.types.has('Sentience')).to.be.true;

			// Check nested types
			expect(result.types.has('Sentience.Consciousness')).to.be.true;
			expect(result.types.has('Sentience.Consciousness.Curiosity')).to.be.true;
			expect(result.types.has('Sentience.Memory')).to.be.true;
		});

		it('should build correct parent-child relationships', () => {
			const fixturePath = path.join(__dirname, 'fixtures', 'ai-topology');
			const result = analyzer.analyzeDirectory(fixturePath);

			const sentience = result.types.get('Sentience');
			const consciousness = result.types.get('Sentience.Consciousness');
			const curiosity = result.types.get('Sentience.Consciousness.Curiosity');

			// Root type has no parent
			expect(sentience?.parent).to.be.undefined;

			// Nested types have correct parents
			expect(consciousness?.parent?.name).to.equal('Sentience');
			expect(curiosity?.parent?.name).to.equal('Consciousness');
		});

		it('should include source file path in type nodes', () => {
			const fixturePath = path.join(__dirname, 'fixtures', 'ai-topology');
			const result = analyzer.analyzeDirectory(fixturePath);

			const sentience = result.types.get('Sentience');
			expect(sentience?.sourceFile).to.include('ai-topology');
		});
	});

	describe('JavaScript directory structures', () => {
		it('should analyze ai-topology-js fixture with .js files', () => {
			const fixturePath = path.join(__dirname, 'fixtures', 'ai-topology-js');
			const result = analyzer.analyzeDirectory(fixturePath);

			expect(result.errors).to.have.length(0);
			expect(result.types.size).to.be.greaterThan(0);

			// Check root type
			expect(result.types.has('Sentience')).to.be.true;

			// Check nested type
			expect(result.types.has('Sentience.Consciousness')).to.be.true;
		});
	});

	describe('ESM (.mjs) directory structures', () => {
		it('should analyze ai-topology-mjs fixture with .mjs files', () => {
			const fixturePath = path.join(__dirname, 'fixtures', 'ai-topology-mjs');
			const result = analyzer.analyzeDirectory(fixturePath);

			expect(result.errors).to.have.length(0);
			expect(result.types.size).to.be.greaterThan(0);

			// Check root type
			expect(result.types.has('Sentience')).to.be.true;

			// Check nested type
			expect(result.types.has('Sentience.Consciousness')).to.be.true;
		});
	});

	describe('Error handling', () => {
		it('should report error for non-existent directory', () => {
			const result = analyzer.analyzeDirectory('/non/existent/path');

			expect(result.errors).to.have.length.greaterThan(0);
			expect(result.errors[0]).to.include('does not exist');
		});

		it('should report error for file instead of directory', () => {
			const filePath = path.join(__dirname, 'fixtures', 'ai-topology', 'Sentience', 'index.ts');
			const result = analyzer.analyzeDirectory(filePath);

			expect(result.errors).to.have.length.greaterThan(0);
			expect(result.errors[0]).to.include('not a directory');
		});
	});

	describe('Graph integration', () => {
		it('should return types compatible with TypeGraphImpl', () => {
			const fixturePath = path.join(__dirname, 'fixtures', 'ai-topology');
			const result = analyzer.analyzeDirectory(fixturePath);

			const graph = new TypeGraphImpl();

			// First pass: add root types
			for (const [, typeNode] of result.types) {
				if (!typeNode.parent) {
					graph.addRoot(typeNode);
				}
			}

			// Second pass: add child types via addChild
			for (const [, typeNode] of result.types) {
				if (typeNode.parent) {
					const parent = graph.allTypes.get(typeNode.parent.fullPath);
					if (parent) {
						graph.addChild(parent, typeNode);
					}
				}
			}

			// Verify graph has the types
			expect(graph.roots.has('Sentience')).to.be.true;
			expect(graph.allTypes.has('Sentience')).to.be.true;
			expect(graph.allTypes.has('Sentience.Consciousness')).to.be.true;
		});

		it('should allow BFS traversal of types', () => {
			const fixturePath = path.join(__dirname, 'fixtures', 'ai-topology');
			const result = analyzer.analyzeDirectory(fixturePath);

			const graph = new TypeGraphImpl();

			// Build graph with proper parent-child relationships
			for (const [, typeNode] of result.types) {
				if (!typeNode.parent) {
					graph.addRoot(typeNode);
				} else {
					// Parent should already be in graph
					const parent = graph.allTypes.get(typeNode.parent.fullPath);
					if (parent) {
						graph.addChild(parent, typeNode);
					}
				}
			}

			// Collect all types via BFS
			const bfsTypes: string[] = [];
			for (const node of graph.bfs()) {
				bfsTypes.push(node.name);
			}

			expect(bfsTypes).to.include('Sentience');
			expect(bfsTypes).to.include('Consciousness');
			expect(bfsTypes).to.include('Memory');
		});
	});

	describe('getGraph() method', () => {
		it('should return the internal TypeGraphImpl', () => {
			const fixturePath = path.join(__dirname, 'fixtures', 'ai-topology');
			analyzer.analyzeDirectory(fixturePath);

			const graph = analyzer.getGraph();
			expect(graph).to.be.instanceOf(TypeGraphImpl);
			expect(graph.allTypes.size).to.be.greaterThan(0);
		});
	});

	describe('getErrors() method', () => {
		it('should return collected errors', () => {
			analyzer.analyzeDirectory('/non/existent/path');
			const errors = analyzer.getErrors();

			expect(errors).to.be.an('array');
			expect(errors.length).to.be.greaterThan(0);
		});
	});

	describe('type inference paths', () => {
		const fixturePath = path.join(__dirname, 'fixtures', 'type-inference');

		it('should analyze type-inference fixture without errors', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			expect(result.errors).to.have.length(0);
			expect(result.types.has('Complex')).to.be.true;
		});

		it('should infer new Date() as number (timestamp)', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('createdAt')?.type).to.equal('number');
		});

		it('should infer new Map() as Map<any, any>', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('mapData')?.type).to.equal('Map<any, any>');
		});

		it('should infer new Set() as Set<any>', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('setData')?.type).to.equal('Set<any>');
		});

		it('should infer new RegExp() as RegExp', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('regexp')?.type).to.equal('RegExp');
		});

		it('should infer new Array() as Array<any>', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('arrData')?.type).to.equal('Array<any>');
		});

		it('should infer Date.now() as number', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('timestamp')?.type).to.equal('number');
		});

		it('should infer parseInt() as number', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('parsed')?.type).to.equal('number');
		});

		it('should infer parseFloat() as number', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('parsed2')?.type).to.equal('number');
		});

		it('should infer String() as string', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('str')?.type).to.equal('string');
		});

		it('should infer Number() as number', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('num')?.type).to.equal('number');
		});

		it('should infer Boolean() as boolean', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('flag')?.type).to.equal('boolean');
		});

		it('should extract constructor params with primitive types from type alias', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			const params = complex?.constructorParams;
			expect(params).to.be.an('array');
			// tag: string, score: number, enabled: boolean, items: string[]
			const tagParam = params?.find(p => p.name === 'tag');
			const scoreParam = params?.find(p => p.name === 'score');
			const enabledParam = params?.find(p => p.name === 'enabled');
			const itemsParam = params?.find(p => p.name === 'items');
			expect(tagParam?.type).to.equal('string');
			expect(scoreParam?.type).to.equal('number');
			expect(enabledParam?.type).to.equal('boolean');
			expect(itemsParam?.type).to.equal('Array<any>');
		});

		it('should expand type alias to object literal for first param', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			const params = complex?.constructorParams;
			// First param is `data: ComplexData` which should be expanded to { label: string; count: number; active: boolean }
			const dataParam = params?.find(p => p.name === 'data');
			expect(dataParam?.type).to.include('label');
			expect(dataParam?.type).to.include('string');
		});

		it('should detect nested Complex.Nested type', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			expect(result.types.has('Complex.Nested')).to.be.true;
		});

		it('should infer null literal as null', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('nullProp')?.type).to.equal('null');
		});

		it('should infer undefined identifier as any (not a keyword in expression context)', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('undefinedProp')?.type).to.equal('any');
		});

		it('should infer array literal as Array<any>', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('arrLiteral')?.type).to.equal('Array<any>');
		});

		it('should infer object literal as object', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('objLiteral')?.type).to.equal('object');
		});

		it('should infer arithmetic binary expression as any', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('sum')?.type).to.equal('any');
		});

		it('should infer new CustomClass() using class name as type', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('instance')?.type).to.equal('LocalClass');
		});

		it('should infer unknown call expression as any', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('callResult')?.type).to.equal('any');
		});

		it('should infer non-Date.now property access call as any', () => {
			const result = analyzer.analyzeDirectory(fixturePath);
			const complex = result.types.get('Complex');
			expect(complex?.properties.get('floorVal')?.type).to.equal('any');
		});
	});
});
