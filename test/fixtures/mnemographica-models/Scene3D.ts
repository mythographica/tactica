'use strict';

import { define } from 'mnemonica';

export const Scene3D = define('Scene3D', function (this: { createdAt: number }) {
	this.createdAt = Date.now();
});

export const Camera3D = Scene3D.define('Camera3D', function (
	this: { x: number; y: number; z: number; zoom: number; rotationX: number; rotationY: number },
	data: { x: number; y: number; z: number; zoom: number; rotationX: number; rotationY: number }
) {
	this.x = data.x;
	this.y = data.y;
	this.z = data.z;
	this.zoom = data.zoom;
	this.rotationX = data.rotationX;
	this.rotationY = data.rotationY;
});

export const GraphNode3D = Scene3D.define('GraphNode3D', function (
	this: { id: string; label: string; x: number; y: number; z: number; radius: number; color: string },
	data: { id: string; label: string; x: number; y: number; z: number; radius: number; color: string }
) {
	this.id = data.id;
	this.label = data.label;
	this.x = data.x;
	this.y = data.y;
	this.z = data.z;
	this.radius = data.radius;
	this.color = data.color;
});

export const Link3D = GraphNode3D.define('Link3D', function (
	this: { source: unknown; target: unknown; strength: number },
	data: { source: unknown; target: unknown; strength: number }
) {
	this.source = data.source;
	this.target = data.target;
	this.strength = data.strength;
});

export const Tooltip3D = GraphNode3D.define('Tooltip3D', function (
	this: { targetNode: unknown; content: string; visible: boolean },
	data: { targetNode: unknown; content: string; visible: boolean }
) {
	this.targetNode = data.targetNode;
	this.content = data.content;
	this.visible = data.visible;
});

export default Scene3D;
