
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
});
