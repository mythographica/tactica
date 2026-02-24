'use strict';

import { TypeNode, TypeGraph } from './types';

/**
 * Trie-based type graph for storing Mnemonica type hierarchy
 */
export class TypeGraphImpl implements TypeGraph {
	roots: Map<string, TypeNode> = new Map();
	allTypes: Map<string, TypeNode> = new Map();

	addRoot(node: TypeNode): void {
		this.roots.set(node.name, node);
		this.allTypes.set(node.fullPath, node);
	}

	addChild(parent: TypeNode, child: TypeNode): void {
		parent.children.set(child.name, child);
		child.parent = parent;
		this.allTypes.set(child.fullPath, child);
	}

	findType(fullPath: string): TypeNode | undefined {
		return this.allTypes.get(fullPath);
	}

	getAllTypes(): TypeNode[] {
		return Array.from(this.allTypes.values());
	}

	clear(): void {
		this.roots.clear();
		this.allTypes.clear();
	}

	/**
	 * Create a new TypeNode
	 */
	static createNode(
		name: string,
		parent: TypeNode | undefined,
		sourceFile: string,
		line: number,
		column: number
	): TypeNode {
		const fullPath = parent ? `${parent.fullPath}.${name}` : name;
		return {
			name,
			fullPath,
			properties: new Map(),
			parent,
			children: new Map(),
			sourceFile,
			line,
			column,
		};
	}

	/**
	 * Traverse the graph in breadth-first order
	 */
	*bfs(): Generator<TypeNode> {
		const visited = new Set<string>();
		const queue: TypeNode[] = Array.from(this.roots.values());

		while (queue.length > 0) {
			const node = queue.shift()!;
			if (visited.has(node.fullPath)) {
				continue;
			}
			visited.add(node.fullPath);
			yield node;

			for (const child of node.children.values()) {
				queue.push(child);
			}
		}
	}

	/**
	 * Traverse the graph in depth-first order
	 */
	*dfs(node?: TypeNode, visited = new Set<string>()): Generator<TypeNode> {
		const startNode = node || this.roots.values().next().value;
		if (!startNode || visited.has(startNode.fullPath)) {
			return;
		}

		visited.add(startNode.fullPath);
		yield startNode;

		for (const child of startNode.children.values()) {
			yield* this.dfs(child, visited);
		}
	}
}
