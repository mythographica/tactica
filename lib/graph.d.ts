import { TypeNode, TypeGraph } from './types';
/**
 * Trie-based type graph for storing Mnemonica type hierarchy
 */
export declare class TypeGraphImpl implements TypeGraph {
    roots: Map<string, TypeNode>;
    allTypes: Map<string, TypeNode>;
    addRoot(node: TypeNode): void;
    addChild(parent: TypeNode, child: TypeNode): void;
    findType(fullPath: string): TypeNode | undefined;
    getAllTypes(): TypeNode[];
    clear(): void;
    /**
     * Create a new TypeNode
     */
    static createNode(name: string, parent: TypeNode | undefined, sourceFile: string, line: number, column: number): TypeNode;
    /**
     * Traverse the graph in breadth-first order
     */
    bfs(): Generator<TypeNode>;
    /**
     * Traverse the graph in depth-first order
     */
    dfs(node?: TypeNode, visited?: Set<string>): Generator<TypeNode>;
}
