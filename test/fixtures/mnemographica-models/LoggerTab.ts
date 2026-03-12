'use strict';

import { define } from 'mnemonica';

export const LoggerTab = define('LoggerTab', function (this: { createdAt: number }) {
	this.createdAt = Date.now();
});

export const LogEntry = LoggerTab.define('LogEntry', function (
	this: { level: 'info' | 'warning' | 'error'; message: string; timestamp: number; typeName?: string; error?: Error; args?: unknown[] },
	data: { level: 'info' | 'warning' | 'error'; message: string; timestamp: number; typeName?: string; error?: Error; args?: unknown[] }
) {
	this.level = data.level;
	this.message = data.message;
	this.timestamp = data.timestamp;
	this.typeName = data.typeName;
	this.error = data.error;
	this.args = data.args;
});

// Note: creationError hook can be registered via MCP when needed
// Example:
// defaultTypes.registerHook('creationError', (hookData) => {
//   logger.LogEntry({ level: 'error', typeName: hookData.typeName, args: hookData.args });
// });

export default LoggerTab;
