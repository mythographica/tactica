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

/**
 * Result of a path-aware mnemonica-graph type reference resolution.
 */
export type GraphTypeReferenceResult =
	| { status: 'unique'; node: TypeNode }
	| { status: 'ambiguous'; candidates: TypeNode[] }
	| { status: 'none' };

/**
 * Path-aware resolution of a mnemonica graph type name, mirroring the
 * runtime lookup law (relative-first, then root; subtypes of different
 * parents may share names legally):
 *   1. self — the anchor's own name (a handler's `this: OwnName`
 *      annotation refers to the type being defined),
 *   2. nearest-chain — walk the anchor's parent chain; the first level
 *      whose subtypes contain the name wins (own subtypes, then up),
 *   3. root — roots of the anchor's collection (default collection when
 *      there is no anchor),
 *   4. program-wide — the unique same-named type anywhere in the graph;
 *      several candidates are a genuine ambiguity.
 * Value-scope anchoring (local bindings / imports) is the caller's tier
 * and runs before this function — see MnemonicaAnalyzer.
 */
export function resolveGraphTypeReference (
	graph: TypeGraphImpl,
	name: string,
	anchor: TypeNode | undefined
): GraphTypeReferenceResult {
	// dotted paths resolve as absolute paths from the collection root
	if (name.includes('.')) {
		const direct = graph.findType(name);
		if (direct) {
			const result: GraphTypeReferenceResult = { status : 'unique', node : direct };
			return result;
		}
		const dottedNoneResult: GraphTypeReferenceResult = { status : 'none' };
		return dottedNoneResult;
	}

	// 1. self — a handler's `this: OwnName` annotation refers to the type
	//    being defined; the anchor node is exactly that type
	if (anchor && anchor.name === name) {
		const selfResult: GraphTypeReferenceResult = { status : 'unique', node : anchor };
		return selfResult;
	}

	// 2. nearest-chain: first level up the anchor chain with a subtype `name`
	let level: TypeNode | undefined = anchor;
	while (level) {
		const child = level.children.get(name);
		if (child) {
			const result: GraphTypeReferenceResult = { status : 'unique', node : child };
			return result;
		}
		level = level.parent;
	}

	// 2. root tier, scoped to the anchor's collection
	const collectionId = anchor?.collectionId;
	const rootMatches: TypeNode[] = [];
	for (const root of graph.roots.values()) {
		if (root.name === name && (root.collectionId ?? undefined) === collectionId) {
			rootMatches.push(root);
		}
	}
	if (rootMatches.length === 1) {
		const result: GraphTypeReferenceResult = { status : 'unique', node : rootMatches[ 0 ] };
		return result;
	}
	if (rootMatches.length > 1) {
		const result: GraphTypeReferenceResult = { status : 'ambiguous', candidates : rootMatches };
		return result;
	}

	// 3. program-wide unique match
	const matches: TypeNode[] = [];
	for (const type of graph.allTypes.values()) {
		if (type.name === name) {
			matches.push(type);
		}
	}
	if (matches.length === 1) {
		const result: GraphTypeReferenceResult = { status : 'unique', node : matches[ 0 ] };
		return result;
	}
	if (matches.length > 1) {
		const result: GraphTypeReferenceResult = { status : 'ambiguous', candidates : matches };
		return result;
	}

	const noneResult: GraphTypeReferenceResult = { status : 'none' };
	return noneResult;
}
