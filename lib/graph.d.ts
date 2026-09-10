import { TypeNode, TypeGraph, HierarchyNode } from './types';
/**
 * Trie-based type graph for storing Mnemonica type hierarchy
 */
export declare class TypeGraphImpl implements TypeGraph {
    /**
     * Keyed by fullPath, not by plain name: a custom collection's root shares
     * its plain name with any other collection (or the default types) — only
     * the `collectionId::`-prefixed fullPath keeps them distinct. Name-keying
     * silently dropped the earlier root, and with it the whole subtree, from
     * every roots-driven walk (generation, hierarchy, verbose tree).
     */
    roots: Map<string, TypeNode>;
    allTypes: Map<string, TypeNode>;
    addRoot(node: TypeNode): void;
    addChild(parent: TypeNode, child: TypeNode): void;
    findType(fullPath: string): TypeNode | undefined;
    /**
     * Find a type by name (search through all types, return first match)
     */
    findTypeByName(name: string): TypeNode | undefined;
    getAllTypes(): TypeNode[];
    clear(): void;
    /**
     * Create a new TypeNode
     */
    static createNode(name: string, parent: TypeNode | undefined, sourceFile: string, line: number, column: number, collectionId?: string): TypeNode;
    /**
     * Traverse the graph in breadth-first order
     */
    bfs(): Generator<TypeNode>;
    /**
     * Traverse the graph in depth-first order
     */
    dfs(node?: TypeNode, visited?: Set<string>): Generator<TypeNode>;
    /**
     * Convert the graph to a structured hierarchy suitable for JSON output.
     */
    toHierarchy(): HierarchyNode[];
    /**
     * Recursively convert a TypeNode to a HierarchyNode.
     */
    private nodeToHierarchy;
}
/**
 * Result of a path-aware mnemonica-graph type reference resolution.
 */
export type GraphTypeReferenceResult = {
    status: 'unique';
    node: TypeNode;
} | {
    status: 'ambiguous';
    candidates: TypeNode[];
} | {
    status: 'none';
};
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
export declare function resolveGraphTypeReference(graph: TypeGraphImpl, name: string, anchor: TypeNode | undefined): GraphTypeReferenceResult;
