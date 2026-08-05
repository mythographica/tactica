'use strict';

import { expect } from 'chai';
import { TypeGraphImpl } from '../src/graph';

describe('TypeGraphImpl', () => {
	let graph: TypeGraphImpl;

	beforeEach(() => {
		graph = new TypeGraphImpl();
	});

	describe('findTypeByName()', () => {
		it('should return a node when found by name', () => {
			const node = TypeGraphImpl.createNode('UserType', undefined, 'test.ts', 1, 1);
			graph.addRoot(node);

			const found = graph.findTypeByName('UserType');
			expect(found).to.equal(node);
		});

		it('should return undefined when name does not exist', () => {
			const node = TypeGraphImpl.createNode('UserType', undefined, 'test.ts', 1, 1);
			graph.addRoot(node);

			const found = graph.findTypeByName('NonExistent');
			expect(found).to.be.undefined;
		});

		it('should find nested types by name', () => {
			const parent = TypeGraphImpl.createNode('Parent', undefined, 'test.ts', 1, 1);
			const child = TypeGraphImpl.createNode('Child', parent, 'test.ts', 5, 1);
			graph.addRoot(parent);
			graph.addChild(parent, child);

			const found = graph.findTypeByName('Child');
			expect(found).to.equal(child);
		});
	});

	describe('clear()', () => {
		it('should clear roots and allTypes', () => {
			const node = TypeGraphImpl.createNode('UserType', undefined, 'test.ts', 1, 1);
			graph.addRoot(node);

			expect(graph.roots.size).to.equal(1);
			expect(graph.allTypes.size).to.equal(1);

			graph.clear();

			expect(graph.roots.size).to.equal(0);
			expect(graph.allTypes.size).to.equal(0);
		});
	});

	describe('bfs()', () => {
		it('should not yield duplicate nodes when same node is reachable via multiple paths', () => {
			const root = TypeGraphImpl.createNode('Root', undefined, 'test.ts', 1, 1);
			const child = TypeGraphImpl.createNode('Child', root, 'test.ts', 5, 1);
			graph.addRoot(root);
			graph.addChild(root, child);
			// Add the same child again under root to simulate duplicate in queue
			root.children.set('Child', child);
			root.children.set('ChildAlias', child);

			const visited: string[] = [];
			for (const node of graph.bfs()) {
				visited.push(node.fullPath);
			}

			// Root.Child should only appear once despite being in queue twice
			const childCount = visited.filter(p => p === 'Root.Child').length;
			expect(childCount).to.equal(1);
		});
	});

	describe('dfs()', () => {
		it('should return immediately when graph is empty', () => {
			const visited: string[] = [];
			for (const node of graph.dfs()) {
				visited.push(node.fullPath);
			}
			expect(visited).to.have.length(0);
		});

		it('should not revisit a node already in visited set', () => {
			const root = TypeGraphImpl.createNode('Root', undefined, 'test.ts', 1, 1);
			graph.addRoot(root);

			const preVisited = new Set<string>([ 'Root' ]);
			const visited: string[] = [];
			for (const node of graph.dfs(root, preVisited)) {
				visited.push(node.fullPath);
			}
			// Root is already visited, so nothing should be yielded
			expect(visited).to.have.length(0);
		});

		it('should traverse all nodes depth-first', () => {
			const root = TypeGraphImpl.createNode('Root', undefined, 'test.ts', 1, 1);
			const a = TypeGraphImpl.createNode('A', root, 'test.ts', 2, 1);
			const b = TypeGraphImpl.createNode('B', root, 'test.ts', 3, 1);
			graph.addRoot(root);
			graph.addChild(root, a);
			graph.addChild(root, b);

			const visited: string[] = [];
			for (const node of graph.dfs(root)) {
				visited.push(node.name);
			}
			expect(visited).to.include('Root');
			expect(visited).to.include('A');
			expect(visited).to.include('B');
			expect(visited).to.have.length(3);
		});
	});

	describe('toHierarchy()', () => {
		it('should return empty array for empty graph', () => {
			const result = graph.toHierarchy();
			expect(result).to.deep.equal([]);
		});

		it('should return a single root with no children', () => {
			const root = TypeGraphImpl.createNode('Root', undefined, 'test.ts', 1, 2);
			graph.addRoot(root);

			const result = graph.toHierarchy();
			expect(result).to.have.length(1);
			expect(result[ 0 ].name).to.equal('Root');
			expect(result[ 0 ].fullPath).to.equal('Root');
			expect(result[ 0 ].location).to.equal('test.ts:1:2');
			expect(result[ 0 ].children).to.deep.equal([]);
		});

		it('should preserve nested children in order', () => {
			const parent = TypeGraphImpl.createNode('Parent', undefined, 'test.ts', 1, 1);
			const child = TypeGraphImpl.createNode('Child', parent, 'test.ts', 5, 1);
			const grandChild = TypeGraphImpl.createNode('GrandChild', child, 'test.ts', 10, 1);
			graph.addRoot(parent);
			graph.addChild(parent, child);
			graph.addChild(child, grandChild);

			const result = graph.toHierarchy();
			expect(result).to.have.length(1);
			expect(result[ 0 ].fullPath).to.equal('Parent');
			expect(result[ 0 ].children[ 0 ].fullPath).to.equal('Parent.Child');
			expect(result[ 0 ].children[ 0 ].children[ 0 ].fullPath).to.equal('Parent.Child.GrandChild');
		});
	});
});
