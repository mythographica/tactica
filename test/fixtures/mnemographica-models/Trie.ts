'use strict';

import { define } from 'mnemonica';

export const Trie = define('Trie', function (this: { createdAt: number }) {
	this.createdAt = Date.now();
});

export const GraphNodeTrie = Trie.define('GraphNodeTrie', function (
	this: { id: string; name: string; path: string; depth: number; isLeaf: boolean },
	data: { id: string; name: string; path: string; depth: number; isLeaf: boolean }
) {
	this.id = data.id;
	this.name = data.name;
	this.path = data.path;
	this.depth = data.depth;
	this.isLeaf = data.isLeaf;
});

export const LinkTrie = GraphNodeTrie.define('LinkTrie', function (
	this: { parent: unknown; child: unknown; relation: 'subtype' | 'instance' },
	data: { parent: unknown; child: unknown; relation: 'subtype' | 'instance' }
) {
	this.parent = data.parent;
	this.child = data.child;
	this.relation = data.relation;
});

export const ContextMenu = GraphNodeTrie.define('ContextMenu', function (
	this: { targetNode: unknown; items: Array<{ label: string; action: string }>; visible: boolean },
	data: { targetNode: unknown; items: Array<{ label: string; action: string }>; visible: boolean }
) {
	this.targetNode = data.targetNode;
	this.items = data.items;
	this.visible = data.visible;
});

export default Trie;
