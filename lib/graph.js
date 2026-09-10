'use strict';
Object.defineProperty(exports, "__esModule", { value: true });
exports.TypeGraphImpl = void 0;
exports.resolveGraphTypeReference = resolveGraphTypeReference;
/**
 * Trie-based type graph for storing Mnemonica type hierarchy
 */
class TypeGraphImpl {
    constructor() {
        /**
         * Keyed by fullPath, not by plain name: a custom collection's root shares
         * its plain name with any other collection (or the default types) — only
         * the `collectionId::`-prefixed fullPath keeps them distinct. Name-keying
         * silently dropped the earlier root, and with it the whole subtree, from
         * every roots-driven walk (generation, hierarchy, verbose tree).
         */
        this.roots = new Map();
        this.allTypes = new Map();
    }
    addRoot(node) {
        this.roots.set(node.fullPath, node);
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
function resolveGraphTypeReference(graph, name, anchor) {
    // dotted paths resolve as absolute paths from the collection root
    if (name.includes('.')) {
        const direct = graph.findType(name);
        if (direct) {
            const result = { status: 'unique', node: direct };
            return result;
        }
        const dottedNoneResult = { status: 'none' };
        return dottedNoneResult;
    }
    // 1. self — a handler's `this: OwnName` annotation refers to the type
    //    being defined; the anchor node is exactly that type
    if (anchor && anchor.name === name) {
        const selfResult = { status: 'unique', node: anchor };
        return selfResult;
    }
    // 2. nearest-chain: first level up the anchor chain with a subtype `name`
    let level = anchor;
    while (level) {
        const child = level.children.get(name);
        if (child) {
            const result = { status: 'unique', node: child };
            return result;
        }
        level = level.parent;
    }
    // 2. root tier, scoped to the anchor's collection
    const collectionId = anchor?.collectionId;
    const rootMatches = [];
    for (const root of graph.roots.values()) {
        if (root.name === name && (root.collectionId ?? undefined) === collectionId) {
            rootMatches.push(root);
        }
    }
    if (rootMatches.length === 1) {
        const result = { status: 'unique', node: rootMatches[0] };
        return result;
    }
    if (rootMatches.length > 1) {
        const result = { status: 'ambiguous', candidates: rootMatches };
        return result;
    }
    // 3. program-wide unique match
    const matches = [];
    for (const type of graph.allTypes.values()) {
        if (type.name === name) {
            matches.push(type);
        }
    }
    if (matches.length === 1) {
        const result = { status: 'unique', node: matches[0] };
        return result;
    }
    if (matches.length > 1) {
        const result = { status: 'ambiguous', candidates: matches };
        return result;
    }
    const noneResult = { status: 'none' };
    return noneResult;
}
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiZ3JhcGguanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvZ3JhcGgudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7QUE0S2IsOERBcUVDO0FBM09EOztHQUVHO0FBQ0gsTUFBYSxhQUFhO0lBQTFCO1FBQ0M7Ozs7OztXQU1HO1FBQ0gsVUFBSyxHQUEwQixJQUFJLEdBQUcsRUFBRSxDQUFDO1FBQ3pDLGFBQVEsR0FBMEIsSUFBSSxHQUFHLEVBQUUsQ0FBQztJQWlJN0MsQ0FBQztJQS9IQSxPQUFPLENBQUUsSUFBYztRQUN0QixJQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxDQUFDO1FBQ3BDLElBQUksQ0FBQyxRQUFRLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLENBQUM7SUFDeEMsQ0FBQztJQUVELFFBQVEsQ0FBRSxNQUFnQixFQUFFLEtBQWU7UUFDMUMsTUFBTSxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztRQUN2QyxLQUFLLENBQUMsTUFBTSxHQUFHLE1BQU0sQ0FBQztRQUN0QixJQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsUUFBUSxFQUFFLEtBQUssQ0FBQyxDQUFDO0lBQzFDLENBQUM7SUFFRCxRQUFRLENBQUUsUUFBZ0I7UUFDekIsT0FBTyxJQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztJQUNwQyxDQUFDO0lBRUQ7O09BRUc7SUFDSCxjQUFjLENBQUUsSUFBWTtRQUMzQixLQUFLLE1BQU0sSUFBSSxJQUFJLElBQUksQ0FBQyxRQUFRLENBQUMsTUFBTSxFQUFFLEVBQUUsQ0FBQztZQUMzQyxJQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssSUFBSSxFQUFFLENBQUM7Z0JBQ3hCLE9BQU8s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LENBQUM7SUFDakUsT0FBTyxVQUFVLENBQUM7QUFDbkIsQ0FBQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0IHtcblx0VHlwZU5vZGUsIFR5cGVHcmFwaCwgSGllcmFyY2h5Tm9kZSBcbn0gZnJvbSAnLi90eXBlcyc7XG5cbi8qKlxuICogVHJpZS1iYXNlZCB0eXBlIGdyYXBoIGZvciBzdG9yaW5nIE1uZW1vbmljYSB0eXBlIGhpZXJhcmNoeVxuICovXG5leHBvcnQgY2xhc3MgVHlwZUdyYXBoSW1wbCBpbXBsZW1lbnRzIFR5cGVHcmFwaCB7XG5cdC8qKlxuXHQgKiBLZXllZCBieSBmdWxsUGF0aCwgbm90IGJ5IHBsYWluIG5hbWU6IGEgY3VzdG9tIGNvbGxlY3Rpb24ncyByb290IHNoYXJlc1xuXHQgKiBpdHMgcGxhaW4gbmFtZSB3aXRoIGFueSBvdGhlciBjb2xsZWN0aW9uIChvciB0aGUgZGVmYXVsdCB0eXBlcykg4oCUIG9ubHlcblx0ICogdGhlIGBjb2xsZWN0aW9uSWQ6OmAtcHJlZml4ZWQgZnVsbFBhdGgga2VlcHMgdGhlbSBkaXN0aW5jdC4gTmFtZS1rZXlpbmdcblx0ICogc2lsZW50bHkgZHJvcHBlZCB0aGUgZWFybGllciByb290LCBhbmQgd2l0aCBpdCB0aGUgd2hvbGUgc3VidHJlZSwgZnJvbVxuXHQgKiBldmVyeSByb290cy1kcml2ZW4gd2FsayAoZ2VuZXJhdGlvbiwgaGllcmFyY2h5LCB2ZXJib3NlIHRyZWUpLlxuXHQgKi9cblx0cm9vdHM6IE1hcDxzdHJpbmcsIFR5cGVOb2RlPiA9IG5ldyBNYXAoKTtcblx0YWxsVHlwZXM6IE1hcDxzdHJpbmcsIFR5cGVOb2RlPiA9IG5ldyBNYXAoKTtcblxuXHRhZGRSb290IChub2RlOiBUeXBlTm9kZSk6IHZvaWQge1xuXHRcdHRoaXMucm9vdHMuc2V0KG5vZGUuZnVsbFBhdGgsIG5vZGUpO1xuXHRcdHRoaXMuYWxsVHlwZXMuc2V0KG5vZGUuZnVsbFBhdGgsIG5vZGUpO1xuXHR9XG5cblx0YWRkQ2hpbGQgKHBhcmVudDogVHlwZU5vZGUsIGNoaWxkOiBUeXBlTm9kZSk6IHZvaWQge1xuXHRcdHBhcmVudC5jaGlsZHJlbi5zZXQoY2hpbGQubmFtZSwgY2hpbGQpO1xuXHRcdGNoaWxkLnBhcmVudCA9IHBhcmVudDtcblx0XHR0aGlzLmFsbFR5cGVzLnNldChjaGlsZC5mdWxsUGF0aCwgY2hpbGQpO1xuXHR9XG5cblx0ZmluZFR5cGUgKGZ1bGxQYXRoOiBzdHJpbmcpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0cmV0dXJuIHRoaXMuYWxsVHlwZXMuZ2V0KGZ1bGxQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBGaW5kIGEgdHlwZSBieSBuYW1lIChzZWFyY2ggdGhyb3VnaCBhbGwgdHlwZXMsIHJldHVybiBmaXJzdCBtYXRjaClcblx0ICovXG5cdGZpbmRUeXBlQnlOYW1lIChuYW1lOiBzdHJpbmcpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCB0eXBlIG9mIHRoaXMuYWxsVHlwZXMudmFsdWVzKCkpIHtcblx0XHRcdGlmICh0eXBlLm5hbWUgPT09IG5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHRnZXRBbGxUeXBlcyAoKTogVHlwZU5vZGVbXSB7XG5cdFx0cmV0dXJuIEFycmF5LmZyb20odGhpcy5hbGxUeXBlcy52YWx1ZXMoKSk7XG5cdH1cblxuXHRjbGVhciAoKTogdm9pZCB7XG5cdFx0dGhpcy5yb290cy5jbGVhcigpO1xuXHRcdHRoaXMuYWxsVHlwZXMuY2xlYXIoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDcmVhdGUgYSBuZXcgVHlwZU5vZGVcblx0ICovXG5cdHN0YXRpYyBjcmVhdGVOb2RlIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0cGFyZW50OiBUeXBlTm9kZSB8IHVuZGVmaW5lZCxcblx0XHRzb3VyY2VGaWxlOiBzdHJpbmcsXG5cdFx0bGluZTogbnVtYmVyLFxuXHRcdGNvbHVtbjogbnVtYmVyLFxuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZ1xuXHQpOiBUeXBlTm9kZSB7XG5cdFx0Y29uc3QgcmVzb2x2ZWRDb2xsZWN0aW9uSWQgPSBjb2xsZWN0aW9uSWQgPz8gcGFyZW50Py5jb2xsZWN0aW9uSWQ7XG5cdFx0Y29uc3QgZnVsbFBhdGggPSBwYXJlbnRcblx0XHRcdD8gYCR7cGFyZW50LmZ1bGxQYXRofS4ke25hbWV9YFxuXHRcdFx0OiByZXNvbHZlZENvbGxlY3Rpb25JZFxuXHRcdFx0XHQ/IGAke3Jlc29sdmVkQ29sbGVjdGlvbklkfTo6JHtuYW1lfWBcblx0XHRcdFx0OiBuYW1lO1xuXHRcdHJldHVybiB7XG5cdFx0XHRuYW1lLFxuXHRcdFx0ZnVsbFBhdGgsXG5cdFx0XHRwcm9wZXJ0aWVzICAgOiBuZXcgTWFwKCksXG5cdFx0XHRwYXJlbnQsXG5cdFx0XHRjaGlsZHJlbiAgICAgOiBuZXcgTWFwKCksXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bGluZSxcblx0XHRcdGNvbHVtbixcblx0XHRcdGNvbGxlY3Rpb25JZCA6IHJlc29sdmVkQ29sbGVjdGlvbklkLFxuXHRcdH07XG5cdH1cblxuXHQvKipcblx0ICogVHJhdmVyc2UgdGhlIGdyYXBoIGluIGJyZWFkdGgtZmlyc3Qgb3JkZXJcblx0ICovXG5cdCpiZnMgKCk6IEdlbmVyYXRvcjxUeXBlTm9kZT4ge1xuXHRcdGNvbnN0IHZpc2l0ZWQgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRjb25zdCBxdWV1ZTogVHlwZU5vZGVbXSA9IEFycmF5LmZyb20odGhpcy5yb290cy52YWx1ZXMoKSk7XG5cblx0XHR3aGlsZSAocXVldWUubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3Qgbm9kZSA9IHF1ZXVlLnNoaWZ0KCkhO1xuXHRcdFx0aWYgKHZpc2l0ZWQuaGFzKG5vZGUuZnVsbFBhdGgpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0dmlzaXRlZC5hZGQobm9kZS5mdWxsUGF0aCk7XG5cdFx0XHR5aWVsZCBub2RlO1xuXG5cdFx0XHRmb3IgKGNvbnN0IGNoaWxkIG9mIG5vZGUuY2hpbGRyZW4udmFsdWVzKCkpIHtcblx0XHRcdFx0cXVldWUucHVzaChjaGlsZCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFRyYXZlcnNlIHRoZSBncmFwaCBpbiBkZXB0aC1maXJzdCBvcmRlclxuXHQgKi9cblx0KmRmcyAobm9kZT86IFR5cGVOb2RlLCB2aXNpdGVkID0gbmV3IFNldDxzdHJpbmc+KCkpOiBHZW5lcmF0b3I8VHlwZU5vZGU+IHtcblx0XHRjb25zdCBzdGFydE5vZGUgPSBub2RlIHx8IHRoaXMucm9vdHMudmFsdWVzKCkubmV4dCgpLnZhbHVlO1xuXHRcdGlmICghc3RhcnROb2RlIHx8IHZpc2l0ZWQuaGFzKHN0YXJ0Tm9kZS5mdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHR2aXNpdGVkLmFkZChzdGFydE5vZGUuZnVsbFBhdGgpO1xuXHRcdHlpZWxkIHN0YXJ0Tm9kZTtcblxuXHRcdGZvciAoY29uc3QgY2hpbGQgb2Ygc3RhcnROb2RlLmNoaWxkcmVuLnZhbHVlcygpKSB7XG5cdFx0XHR5aWVsZCogdGhpcy5kZnMoY2hpbGQsIHZpc2l0ZWQpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb252ZXJ0IHRoZSBncmFwaCB0byBhIHN0cnVjdHVyZWQgaGllcmFyY2h5IHN1aXRhYmxlIGZvciBKU09OIG91dHB1dC5cblx0ICovXG5cdHRvSGllcmFyY2h5ICgpOiBIaWVyYXJjaHlOb2RlW10ge1xuXHRcdGNvbnN0IHJvb3RzID0gQXJyYXkuZnJvbSh0aGlzLnJvb3RzLnZhbHVlcygpKTtcblx0XHRjb25zdCByZXN1bHQgPSByb290cy5tYXAocm9vdCA9PiB0aGlzLm5vZGVUb0hpZXJhcmNoeShyb290KSk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWN1cnNpdmVseSBjb252ZXJ0IGEgVHlwZU5vZGUgdG8gYSBIaWVyYXJjaHlOb2RlLlxuXHQgKi9cblx0cHJpdmF0ZSBub2RlVG9IaWVyYXJjaHkgKG5vZGU6IFR5cGVOb2RlKTogSGllcmFyY2h5Tm9kZSB7XG5cdFx0Y29uc3QgY2hpbGRyZW4gPSBBcnJheS5mcm9tKG5vZGUuY2hpbGRyZW4udmFsdWVzKCkpLm1hcChjaGlsZCA9PlxuXHRcdFx0dGhpcy5ub2RlVG9IaWVyYXJjaHkoY2hpbGQpKTtcblx0XHRjb25zdCByZXN1bHQ6IEhpZXJhcmNoeU5vZGUgPSB7XG5cdFx0XHRuYW1lICAgICA6IG5vZGUubmFtZSxcblx0XHRcdGZ1bGxQYXRoIDogbm9kZS5mdWxsUGF0aCxcblx0XHRcdGxvY2F0aW9uIDogYCR7bm9kZS5zb3VyY2VGaWxlfToke25vZGUubGluZX06JHtub2RlLmNvbHVtbn1gLFxuXHRcdFx0Y2hpbGRyZW4sXG5cdFx0fTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG59XG5cbi8qKlxuICogUmVzdWx0IG9mIGEgcGF0aC1hd2FyZSBtbmVtb25pY2EtZ3JhcGggdHlwZSByZWZlcmVuY2UgcmVzb2x1dGlvbi5cbiAqL1xuZXhwb3J0IHR5cGUgR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0ID1cblx0fCB7IHN0YXR1czogJ3VuaXF1ZSc7IG5vZGU6IFR5cGVOb2RlIH1cblx0fCB7IHN0YXR1czogJ2FtYmlndW91cyc7IGNhbmRpZGF0ZXM6IFR5cGVOb2RlW10gfVxuXHR8IHsgc3RhdHVzOiAnbm9uZScgfTtcblxuLyoqXG4gKiBQYXRoLWF3YXJlIHJlc29sdXRpb24gb2YgYSBtbmVtb25pY2EgZ3JhcGggdHlwZSBuYW1lLCBtaXJyb3JpbmcgdGhlXG4gKiBydW50aW1lIGxvb2t1cCBsYXcgKHJlbGF0aXZlLWZpcnN0LCB0aGVuIHJvb3Q7IHN1YnR5cGVzIG9mIGRpZmZlcmVudFxuICogcGFyZW50cyBtYXkgc2hhcmUgbmFtZXMgbGVnYWxseSk6XG4gKiAgIDEuIHNlbGYg4oCUIHRoZSBhbmNob3IncyBvd24gbmFtZSAoYSBoYW5kbGVyJ3MgYHRoaXM6IE93bk5hbWVgXG4gKiAgICAgIGFubm90YXRpb24gcmVmZXJzIHRvIHRoZSB0eXBlIGJlaW5nIGRlZmluZWQpLFxuICogICAyLiBuZWFyZXN0LWNoYWluIOKAlCB3YWxrIHRoZSBhbmNob3IncyBwYXJlbnQgY2hhaW47IHRoZSBmaXJzdCBsZXZlbFxuICogICAgICB3aG9zZSBzdWJ0eXBlcyBjb250YWluIHRoZSBuYW1lIHdpbnMgKG93biBzdWJ0eXBlcywgdGhlbiB1cCksXG4gKiAgIDMuIHJvb3Qg4oCUIHJvb3RzIG9mIHRoZSBhbmNob3IncyBjb2xsZWN0aW9uIChkZWZhdWx0IGNvbGxlY3Rpb24gd2hlblxuICogICAgICB0aGVyZSBpcyBubyBhbmNob3IpLFxuICogICA0LiBwcm9ncmFtLXdpZGUg4oCUIHRoZSB1bmlxdWUgc2FtZS1uYW1lZCB0eXBlIGFueXdoZXJlIGluIHRoZSBncmFwaDtcbiAqICAgICAgc2V2ZXJhbCBjYW5kaWRhdGVzIGFyZSBhIGdlbnVpbmUgYW1iaWd1aXR5LlxuICogVmFsdWUtc2NvcGUgYW5jaG9yaW5nIChsb2NhbCBiaW5kaW5ncyAvIGltcG9ydHMpIGlzIHRoZSBjYWxsZXIncyB0aWVyXG4gKiBhbmQgcnVucyBiZWZvcmUgdGhpcyBmdW5jdGlvbiDigJQgc2VlIE1uZW1vbmljYUFuYWx5emVyLlxuICovXG5leHBvcnQgZnVuY3Rpb24gcmVzb2x2ZUdyYXBoVHlwZVJlZmVyZW5jZSAoXG5cdGdyYXBoOiBUeXBlR3JhcGhJbXBsLFxuXHRuYW1lOiBzdHJpbmcsXG5cdGFuY2hvcjogVHlwZU5vZGUgfCB1bmRlZmluZWRcbik6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCB7XG5cdC8vIGRvdHRlZCBwYXRocyByZXNvbHZlIGFzIGFic29sdXRlIHBhdGhzIGZyb20gdGhlIGNvbGxlY3Rpb24gcm9vdFxuXHRpZiAobmFtZS5pbmNsdWRlcygnLicpKSB7XG5cdFx0Y29uc3QgZGlyZWN0ID0gZ3JhcGguZmluZFR5cGUobmFtZSk7XG5cdFx0aWYgKGRpcmVjdCkge1xuXHRcdFx0Y29uc3QgcmVzdWx0OiBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQgPSB7IHN0YXR1cyA6ICd1bmlxdWUnLCBub2RlIDogZGlyZWN0IH07XG5cdFx0XHRyZXR1cm4gcmVzdWx0O1xuXHRcdH1cblx0XHRjb25zdCBkb3R0ZWROb25lUmVzdWx0OiBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQgPSB7IHN0YXR1cyA6ICdub25lJyB9O1xuXHRcdHJldHVybiBkb3R0ZWROb25lUmVzdWx0O1xuXHR9XG5cblx0Ly8gMS4gc2VsZiDigJQgYSBoYW5kbGVyJ3MgYHRoaXM6IE93bk5hbWVgIGFubm90YXRpb24gcmVmZXJzIHRvIHRoZSB0eXBlXG5cdC8vICAgIGJlaW5nIGRlZmluZWQ7IHRoZSBhbmNob3Igbm9kZSBpcyBleGFjdGx5IHRoYXQgdHlwZVxuXHRpZiAoYW5jaG9yICYmIGFuY2hvci5uYW1lID09PSBuYW1lKSB7XG5cdFx0Y29uc3Qgc2VsZlJlc3VsdDogR3JhcGhUeXBlUmVmZXJlbmNlUmVzdWx0ID0geyBzdGF0dXMgOiAndW5pcXVlJywgbm9kZSA6IGFuY2hvciB9O1xuXHRcdHJldHVybiBzZWxmUmVzdWx0O1xuXHR9XG5cblx0Ly8gMi4gbmVhcmVzdC1jaGFpbjogZmlyc3QgbGV2ZWwgdXAgdGhlIGFuY2hvciBjaGFpbiB3aXRoIGEgc3VidHlwZSBgbmFtZWBcblx0bGV0IGxldmVsOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCA9IGFuY2hvcjtcblx0d2hpbGUgKGxldmVsKSB7XG5cdFx0Y29uc3QgY2hpbGQgPSBsZXZlbC5jaGlsZHJlbi5nZXQobmFtZSk7XG5cdFx0aWYgKGNoaWxkKSB7XG5cdFx0XHRjb25zdCByZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgOiBjaGlsZCB9O1xuXHRcdFx0cmV0dXJuIHJlc3VsdDtcblx0XHR9XG5cdFx0bGV2ZWwgPSBsZXZlbC5wYXJlbnQ7XG5cdH1cblxuXHQvLyAyLiByb290IHRpZXIsIHNjb3BlZCB0byB0aGUgYW5jaG9yJ3MgY29sbGVjdGlvblxuXHRjb25zdCBjb2xsZWN0aW9uSWQgPSBhbmNob3I/LmNvbGxlY3Rpb25JZDtcblx0Y29uc3Qgcm9vdE1hdGNoZXM6IFR5cGVOb2RlW10gPSBbXTtcblx0Zm9yIChjb25zdCByb290IG9mIGdyYXBoLnJvb3RzLnZhbHVlcygpKSB7XG5cdFx0aWYgKHJvb3QubmFtZSA9PT0gbmFtZSAmJiAocm9vdC5jb2xsZWN0aW9uSWQgPz8gdW5kZWZpbmVkKSA9PT0gY29sbGVjdGlvbklkKSB7XG5cdFx0XHRyb290TWF0Y2hlcy5wdXNoKHJvb3QpO1xuXHRcdH1cblx0fVxuXHRpZiAocm9vdE1hdGNoZXMubGVuZ3RoID09PSAxKSB7XG5cdFx0Y29uc3QgcmVzdWx0OiBHcmFwaFR5cGVSZWZlcmVuY2VSZXN1bHQgPSB7IHN0YXR1cyA6ICd1bmlxdWUnLCBub2RlIDogcm9vdE1hdGNoZXNbIDAgXSB9O1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblx0aWYgKHJvb3RNYXRjaGVzLmxlbmd0aCA+IDEpIHtcblx0XHRjb25zdCByZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ2FtYmlndW91cycsIGNhbmRpZGF0ZXMgOiByb290TWF0Y2hlcyB9O1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvLyAzLiBwcm9ncmFtLXdpZGUgdW5pcXVlIG1hdGNoXG5cdGNvbnN0IG1hdGNoZXM6IFR5cGVOb2RlW10gPSBbXTtcblx0Zm9yIChjb25zdCB0eXBlIG9mIGdyYXBoLmFsbFR5cGVzLnZhbHVlcygpKSB7XG5cdFx0aWYgKHR5cGUubmFtZSA9PT0gbmFtZSkge1xuXHRcdFx0bWF0Y2hlcy5wdXNoKHR5cGUpO1xuXHRcdH1cblx0fVxuXHRpZiAobWF0Y2hlcy5sZW5ndGggPT09IDEpIHtcblx0XHRjb25zdCByZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ3VuaXF1ZScsIG5vZGUgOiBtYXRjaGVzWyAwIF0gfTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cdGlmIChtYXRjaGVzLmxlbmd0aCA+IDEpIHtcblx0XHRjb25zdCByZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ2FtYmlndW91cycsIGNhbmRpZGF0ZXMgOiBtYXRjaGVzIH07XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdGNvbnN0IG5vbmVSZXN1bHQ6IEdyYXBoVHlwZVJlZmVyZW5jZVJlc3VsdCA9IHsgc3RhdHVzIDogJ25vbmUnIH07XG5cdHJldHVybiBub25lUmVzdWx0O1xufVxuIl19