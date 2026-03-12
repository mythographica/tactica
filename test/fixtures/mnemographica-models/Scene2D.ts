'use strict';

import { define } from 'mnemonica';

export const Scene2D = define('Scene2D', function (this: { createdAt: number }) {
	this.createdAt = Date.now();
});

export const Camera2D = Scene2D.define('Camera2D', function (
	this: { x: number; y: number; zoom: number },
	data: { x: number; y: number; zoom: number }
) {
	this.x = data.x;
	this.y = data.y;
	this.zoom = data.zoom;
});

export const GraphNode2D = Scene2D.define('GraphNode2D', function (
	this: { id: string; label: string; x: number; y: number; radius: number; color: string },
	data: { id: string; label: string; x: number; y: number; radius: number; color: string }
) {
	this.id = data.id;
	this.label = data.label;
	this.x = data.x;
	this.y = data.y;
	this.radius = data.radius;
	this.color = data.color;
});

export const Link2D = GraphNode2D.define('Link2D', function (
	this: { source: unknown; target: unknown; strength: number },
	data: { source: unknown; target: unknown; strength: number }
) {
	this.source = data.source;
	this.target = data.target;
	this.strength = data.strength;
});

export const Tooltip2D = GraphNode2D.define('Tooltip2D', function (
	this: { targetNode: unknown; content: string; visible: boolean },
	data: { targetNode: unknown; content: string; visible: boolean }
) {
	this.targetNode = data.targetNode;
	this.content = data.content;
	this.visible = data.visible;
});

export default Scene2D;
