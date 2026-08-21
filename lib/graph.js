'use strict';
Object.defineProperty(exports, "__esModule", { value: true });
exports.TypeGraphImpl = void 0;
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
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiZ3JhcGguanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvZ3JhcGgudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsWUFBWSxDQUFDOzs7QUFNYjs7R0FFRztBQUNILE1BQWEsYUFBYTtJQUExQjtRQUNDOzs7Ozs7V0FNRztRQUNILFVBQUssR0FBMEIsSUFBSSxHQUFHLEVBQUUsQ0FBQztRQUN6QyxhQUFRLEdBQTBCLElBQUksR0FBRyxFQUFFLENBQUM7SUFpSTdDLENBQUM7SUEvSEEsT0FBTyxDQUFFLElBQWM7UUFDdEIsSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMsQ0FBQztRQUNwQyxJQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxDQUFDO0lBQ3hDLENBQUM7SUFFRCxRQUFRLENBQUUsTUFBZ0IsRUFBRSxLQUFlO1FBQzFDLE1BQU0sQ0FBQyxRQUFRLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsS0FBSyxDQUFDLENBQUM7UUFDdkMsS0FBSyxDQUFDLE1BQU0sR0FBRyxNQUFNLENBQUM7UUFDdEIsSUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLFFBQVEsRUFBRSxLQUFLLENBQUMsQ0FBQztJQUMxQyxDQUFDO0lBRUQsUUFBUSxDQUFFLFFBQWdCO1FBQ3pCLE9BQU8sSUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUM7SUFDcEMsQ0FBQztJQUVEOztPQUVHO0lBQ0gsY0FBYyxDQUFFLElBQVk7UUFDM0IsS0FBSyxNQUFNLElBQUksSUFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLE1BQU0sRUFBRSxFQUFFLENBQUM7WUFDM0MsSUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLElBQUksRUFBRSxDQUFDO2dCQUN4QixPQUFPLElBQUksQ0FBQztZQUNi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LElBQUksQ0FBQyxLQUFLLENBQUMsTUFBTSxFQUFFLENBQUMsQ0FBQztRQUM5QyxNQUFNLE1BQU0sR0FBRyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDO1FBQzdELE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOztPQUVHO0lBQ0ssZUFBZSxDQUFFLElBQWM7UUFDdEMsTUFBTSxRQUFRLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFLENBQy9ELElBQUksQ0FBQyxlQUFlLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQztRQUM5QixNQUFNLE1BQU0sR0FBa0I7WUFDN0IsSUFBSSxFQUFPLElBQUksQ0FBQyxJQUFJO1lBQ3BCLFFBQVEsRUFBRyxJQUFJLENBQUMsUUFBUTtZQUN4QixRQUFRLEVBQUcsR0FBRyxJQUFJLENBQUMsVUFBVSxJQUFJLElBQUksQ0FBQyxJQUFJLElBQUksSUFBSSxDQUFDLE1BQU0sRUFBRTtZQUMzRCxRQUFRO1NBQ1IsQ0FBQztRQUNGLE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztDQUNEO0FBMUlELHNDQTBJQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0IHtcblx0VHlwZU5vZGUsIFR5cGVHcmFwaCwgSGllcmFyY2h5Tm9kZSBcbn0gZnJvbSAnLi90eXBlcyc7XG5cbi8qKlxuICogVHJpZS1iYXNlZCB0eXBlIGdyYXBoIGZvciBzdG9yaW5nIE1uZW1vbmljYSB0eXBlIGhpZXJhcmNoeVxuICovXG5leHBvcnQgY2xhc3MgVHlwZUdyYXBoSW1wbCBpbXBsZW1lbnRzIFR5cGVHcmFwaCB7XG5cdC8qKlxuXHQgKiBLZXllZCBieSBmdWxsUGF0aCwgbm90IGJ5IHBsYWluIG5hbWU6IGEgY3VzdG9tIGNvbGxlY3Rpb24ncyByb290IHNoYXJlc1xuXHQgKiBpdHMgcGxhaW4gbmFtZSB3aXRoIGFueSBvdGhlciBjb2xsZWN0aW9uIChvciB0aGUgZGVmYXVsdCB0eXBlcykg4oCUIG9ubHlcblx0ICogdGhlIGBjb2xsZWN0aW9uSWQ6OmAtcHJlZml4ZWQgZnVsbFBhdGgga2VlcHMgdGhlbSBkaXN0aW5jdC4gTmFtZS1rZXlpbmdcblx0ICogc2lsZW50bHkgZHJvcHBlZCB0aGUgZWFybGllciByb290LCBhbmQgd2l0aCBpdCB0aGUgd2hvbGUgc3VidHJlZSwgZnJvbVxuXHQgKiBldmVyeSByb290cy1kcml2ZW4gd2FsayAoZ2VuZXJhdGlvbiwgaGllcmFyY2h5LCB2ZXJib3NlIHRyZWUpLlxuXHQgKi9cblx0cm9vdHM6IE1hcDxzdHJpbmcsIFR5cGVOb2RlPiA9IG5ldyBNYXAoKTtcblx0YWxsVHlwZXM6IE1hcDxzdHJpbmcsIFR5cGVOb2RlPiA9IG5ldyBNYXAoKTtcblxuXHRhZGRSb290IChub2RlOiBUeXBlTm9kZSk6IHZvaWQge1xuXHRcdHRoaXMucm9vdHMuc2V0KG5vZGUuZnVsbFBhdGgsIG5vZGUpO1xuXHRcdHRoaXMuYWxsVHlwZXMuc2V0KG5vZGUuZnVsbFBhdGgsIG5vZGUpO1xuXHR9XG5cblx0YWRkQ2hpbGQgKHBhcmVudDogVHlwZU5vZGUsIGNoaWxkOiBUeXBlTm9kZSk6IHZvaWQge1xuXHRcdHBhcmVudC5jaGlsZHJlbi5zZXQoY2hpbGQubmFtZSwgY2hpbGQpO1xuXHRcdGNoaWxkLnBhcmVudCA9IHBhcmVudDtcblx0XHR0aGlzLmFsbFR5cGVzLnNldChjaGlsZC5mdWxsUGF0aCwgY2hpbGQpO1xuXHR9XG5cblx0ZmluZFR5cGUgKGZ1bGxQYXRoOiBzdHJpbmcpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0cmV0dXJuIHRoaXMuYWxsVHlwZXMuZ2V0KGZ1bGxQYXRoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBGaW5kIGEgdHlwZSBieSBuYW1lIChzZWFyY2ggdGhyb3VnaCBhbGwgdHlwZXMsIHJldHVybiBmaXJzdCBtYXRjaClcblx0ICovXG5cdGZpbmRUeXBlQnlOYW1lIChuYW1lOiBzdHJpbmcpOiBUeXBlTm9kZSB8IHVuZGVmaW5lZCB7XG5cdFx0Zm9yIChjb25zdCB0eXBlIG9mIHRoaXMuYWxsVHlwZXMudmFsdWVzKCkpIHtcblx0XHRcdGlmICh0eXBlLm5hbWUgPT09IG5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIHR5cGU7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiB1bmRlZmluZWQ7XG5cdH1cblxuXHRnZXRBbGxUeXBlcyAoKTogVHlwZU5vZGVbXSB7XG5cdFx0cmV0dXJuIEFycmF5LmZyb20odGhpcy5hbGxUeXBlcy52YWx1ZXMoKSk7XG5cdH1cblxuXHRjbGVhciAoKTogdm9pZCB7XG5cdFx0dGhpcy5yb290cy5jbGVhcigpO1xuXHRcdHRoaXMuYWxsVHlwZXMuY2xlYXIoKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBDcmVhdGUgYSBuZXcgVHlwZU5vZGVcblx0ICovXG5cdHN0YXRpYyBjcmVhdGVOb2RlIChcblx0XHRuYW1lOiBzdHJpbmcsXG5cdFx0cGFyZW50OiBUeXBlTm9kZSB8IHVuZGVmaW5lZCxcblx0XHRzb3VyY2VGaWxlOiBzdHJpbmcsXG5cdFx0bGluZTogbnVtYmVyLFxuXHRcdGNvbHVtbjogbnVtYmVyLFxuXHRcdGNvbGxlY3Rpb25JZD86IHN0cmluZ1xuXHQpOiBUeXBlTm9kZSB7XG5cdFx0Y29uc3QgcmVzb2x2ZWRDb2xsZWN0aW9uSWQgPSBjb2xsZWN0aW9uSWQgPz8gcGFyZW50Py5jb2xsZWN0aW9uSWQ7XG5cdFx0Y29uc3QgZnVsbFBhdGggPSBwYXJlbnRcblx0XHRcdD8gYCR7cGFyZW50LmZ1bGxQYXRofS4ke25hbWV9YFxuXHRcdFx0OiByZXNvbHZlZENvbGxlY3Rpb25JZFxuXHRcdFx0XHQ/IGAke3Jlc29sdmVkQ29sbGVjdGlvbklkfTo6JHtuYW1lfWBcblx0XHRcdFx0OiBuYW1lO1xuXHRcdHJldHVybiB7XG5cdFx0XHRuYW1lLFxuXHRcdFx0ZnVsbFBhdGgsXG5cdFx0XHRwcm9wZXJ0aWVzICAgOiBuZXcgTWFwKCksXG5cdFx0XHRwYXJlbnQsXG5cdFx0XHRjaGlsZHJlbiAgICAgOiBuZXcgTWFwKCksXG5cdFx0XHRzb3VyY2VGaWxlLFxuXHRcdFx0bGluZSxcblx0XHRcdGNvbHVtbixcblx0XHRcdGNvbGxlY3Rpb25JZCA6IHJlc29sdmVkQ29sbGVjdGlvbklkLFxuXHRcdH07XG5cdH1cblxuXHQvKipcblx0ICogVHJhdmVyc2UgdGhlIGdyYXBoIGluIGJyZWFkdGgtZmlyc3Qgb3JkZXJcblx0ICovXG5cdCpiZnMgKCk6IEdlbmVyYXRvcjxUeXBlTm9kZT4ge1xuXHRcdGNvbnN0IHZpc2l0ZWQgPSBuZXcgU2V0PHN0cmluZz4oKTtcblx0XHRjb25zdCBxdWV1ZTogVHlwZU5vZGVbXSA9IEFycmF5LmZyb20odGhpcy5yb290cy52YWx1ZXMoKSk7XG5cblx0XHR3aGlsZSAocXVldWUubGVuZ3RoID4gMCkge1xuXHRcdFx0Y29uc3Qgbm9kZSA9IHF1ZXVlLnNoaWZ0KCkhO1xuXHRcdFx0aWYgKHZpc2l0ZWQuaGFzKG5vZGUuZnVsbFBhdGgpKSB7XG5cdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0fVxuXHRcdFx0dmlzaXRlZC5hZGQobm9kZS5mdWxsUGF0aCk7XG5cdFx0XHR5aWVsZCBub2RlO1xuXG5cdFx0XHRmb3IgKGNvbnN0IGNoaWxkIG9mIG5vZGUuY2hpbGRyZW4udmFsdWVzKCkpIHtcblx0XHRcdFx0cXVldWUucHVzaChjaGlsZCk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIFRyYXZlcnNlIHRoZSBncmFwaCBpbiBkZXB0aC1maXJzdCBvcmRlclxuXHQgKi9cblx0KmRmcyAobm9kZT86IFR5cGVOb2RlLCB2aXNpdGVkID0gbmV3IFNldDxzdHJpbmc+KCkpOiBHZW5lcmF0b3I8VHlwZU5vZGU+IHtcblx0XHRjb25zdCBzdGFydE5vZGUgPSBub2RlIHx8IHRoaXMucm9vdHMudmFsdWVzKCkubmV4dCgpLnZhbHVlO1xuXHRcdGlmICghc3RhcnROb2RlIHx8IHZpc2l0ZWQuaGFzKHN0YXJ0Tm9kZS5mdWxsUGF0aCkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cblx0XHR2aXNpdGVkLmFkZChzdGFydE5vZGUuZnVsbFBhdGgpO1xuXHRcdHlpZWxkIHN0YXJ0Tm9kZTtcblxuXHRcdGZvciAoY29uc3QgY2hpbGQgb2Ygc3RhcnROb2RlLmNoaWxkcmVuLnZhbHVlcygpKSB7XG5cdFx0XHR5aWVsZCogdGhpcy5kZnMoY2hpbGQsIHZpc2l0ZWQpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHQgKiBDb252ZXJ0IHRoZSBncmFwaCB0byBhIHN0cnVjdHVyZWQgaGllcmFyY2h5IHN1aXRhYmxlIGZvciBKU09OIG91dHB1dC5cblx0ICovXG5cdHRvSGllcmFyY2h5ICgpOiBIaWVyYXJjaHlOb2RlW10ge1xuXHRcdGNvbnN0IHJvb3RzID0gQXJyYXkuZnJvbSh0aGlzLnJvb3RzLnZhbHVlcygpKTtcblx0XHRjb25zdCByZXN1bHQgPSByb290cy5tYXAocm9vdCA9PiB0aGlzLm5vZGVUb0hpZXJhcmNoeShyb290KSk7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZWN1cnNpdmVseSBjb252ZXJ0IGEgVHlwZU5vZGUgdG8gYSBIaWVyYXJjaHlOb2RlLlxuXHQgKi9cblx0cHJpdmF0ZSBub2RlVG9IaWVyYXJjaHkgKG5vZGU6IFR5cGVOb2RlKTogSGllcmFyY2h5Tm9kZSB7XG5cdFx0Y29uc3QgY2hpbGRyZW4gPSBBcnJheS5mcm9tKG5vZGUuY2hpbGRyZW4udmFsdWVzKCkpLm1hcChjaGlsZCA9PlxuXHRcdFx0dGhpcy5ub2RlVG9IaWVyYXJjaHkoY2hpbGQpKTtcblx0XHRjb25zdCByZXN1bHQ6IEhpZXJhcmNoeU5vZGUgPSB7XG5cdFx0XHRuYW1lICAgICA6IG5vZGUubmFtZSxcblx0XHRcdGZ1bGxQYXRoIDogbm9kZS5mdWxsUGF0aCxcblx0XHRcdGxvY2F0aW9uIDogYCR7bm9kZS5zb3VyY2VGaWxlfToke25vZGUubGluZX06JHtub2RlLmNvbHVtbn1gLFxuXHRcdFx0Y2hpbGRyZW4sXG5cdFx0fTtcblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG59XG4iXX0=