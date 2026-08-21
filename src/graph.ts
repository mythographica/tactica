'use strict';

import {
	TypeNode, TypeGraph, HierarchyNode 
} from './types';

/**
 * Trie-based type graph for storing Mnemonica type hierarchy
 */
export class TypeGraphImpl implements TypeGraph {
	/**
	 * Keyed by fullPath, not by plain name: a custom collection's root shares
	 * its plain name with any other collection (or the default types) — only
	 * the `collectionId::`-prefixed fullPath keeps them distinct. Name-keying
	 * silently dropped the earlier root, and with it the whole subtree, from
	 * every roots-driven walk (generation, hierarchy, verbose tree).
	 */
	roots: Map<string, TypeNode> = new Map();
	allTypes: Map<string, TypeNode> = new Map();

	addRoot (node: TypeNode): void {
		this.roots.set(node.fullPath, node);
		this.allTypes.set(node.fullPath, node);
	}

	addChild (parent: TypeNode, child: TypeNode): void {
		parent.children.set(child.name, child);
		child.parent = parent;
		this.allTypes.set(child.fullPath, child);
	}

	findType (fullPath: string): TypeNode | undefined {
		return this.allTypes.get(fullPath);
	}

	/**
	 * Find a type by name (search through all types, return first match)
	 */
	findTypeByName (name: string): TypeNode | undefined {
		for (const type of this.allTypes.values()) {
			if (type.name === name) {
				return type;
			}
		}
		return undefined;
	}

	getAllTypes (): TypeNode[] {
		return Array.from(this.allTypes.values());
	}

	clear (): void {
		this.roots.clear();
		this.allTypes.clear();
	}

	/**
	 * Create a new TypeNode
	 */
	static createNode (
		name: string,
		parent: TypeNode | undefined,
		sourceFile: string,
		line: number,
		column: number,
		collectionId?: string
	): TypeNode {
		const resolvedCollectionId = collectionId ?? parent?.collectionId;
		const fullPath = parent
			? `${parent.fullPath}.${name}`
			: resolvedCollectionId
				? `${resolvedCollectionId}::${name}`
				: name;
		return {
			name,
			fullPath,
			properties   : new Map(),
			parent,
			children     : new Map(),
			sourceFile,
			line,
			column,
			collectionId : resolvedCollectionId,
		};
	}

	/**
	 * Traverse the graph in breadth-first order
	 */
	*bfs (): Generator<TypeNode> {
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
	*dfs (node?: TypeNode, visited = new Set<string>()): Generator<TypeNode> {
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

	/**
	 * Convert the graph to a structured hierarchy suitable for JSON output.
	 */
	toHierarchy (): HierarchyNode[] {
		const roots = Array.from(this.roots.values());
		const result = roots.map(root => this.nodeToHierarchy(root));
		return result;
	}

	/**
	 * Recursively convert a TypeNode to a HierarchyNode.
	 */
	private nodeToHierarchy (node: TypeNode): HierarchyNode {
		const children = Array.from(node.children.values()).map(child =>
			this.nodeToHierarchy(child));
		const result: HierarchyNode = {
			name     : node.name,
			fullPath : node.fullPath,
			location : `${node.sourceFile}:${node.line}:${node.column}`,
			children,
		};
		return result;
	}
}
