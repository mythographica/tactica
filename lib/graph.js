'use strict';
Object.defineProperty(exports, "__esModule", { value: true });
exports.TypeGraphImpl = void 0;
/**
 * Trie-based type graph for storing Mnemonica type hierarchy
 */
class TypeGraphImpl {
    constructor() {
        this.roots = new Map();
        this.allTypes = new Map();
    }
    addRoot(node) {
        this.roots.set(node.name, node);
        this.allTypes.set(node.fullPath, node);
    }
    addChild(parent, child) {
        parent.children.set(child.name, child);
        child.parent = parent;
        this.allTypes.set(child.fullPath, child);
    }
    findType(fullPath) {
        return this.allTypes.get(fullPath);
    }
    /**
     * Find a type by name (search through all types, return first match)
     */
    findTypeByName(name) {
        for (const type of this.allTypes.values()) {
            if (type.name === name) {
                return type;
            }
        }
        return undefined;
    }
    getAllTypes() {
        return Array.from(this.allTypes.values());
    }
    clear() {
        this.roots.clear();
        this.allTypes.clear();
    }
    /**
     * Create a new TypeNode
     */
    static createNode(name, parent, sourceFile, line, column, collectionId) {
        const resolvedCollectionId = collectionId ?? parent?.collectionId;
        const fullPath = parent
            ? `${parent.fullPath}.${name}`
            : resolvedCollectionId
                ? `${resolvedCollectionId}::${name}`
                : name;
        return {
            name,
            fullPath,
            properties: new Map(),
            parent,
            children: new Map(),
            sourceFile,
            line,
            column,
            collectionId: resolvedCollectionId,
        };
    }
    /**
     * Traverse the graph in breadth-first order
     */
    *bfs() {
        const visited = new Set();
        const queue = Array.from(this.roots.values());
        while (queue.length > 0) {
            const node = queue.shift();
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
    *dfs(node, visited = new Set()) {
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
    toHierarchy() {
        const roots = Array.from(this.roots.values());
        const result = roots.map(root => this.nodeToHierarchy(root));
        return result;
    }
    /**
     * Recursively convert a TypeNode to a HierarchyNode.
     */
    nodeToHierarchy(node) {
        const children = Array.from(node.children.values()).map(child => this.nodeToHierarchy(child));
        const result = {
            name: node.name,
            fullPath: node.fullPath,
            location: `${node.sourceFile}:${node.line}:${node.column}`,
            children,
        };
        return result;
    }
}
exports.TypeGraphImpl = TypeGraphImpl;
//# sourceMappingURL=graph.js.map