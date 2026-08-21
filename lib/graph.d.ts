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
