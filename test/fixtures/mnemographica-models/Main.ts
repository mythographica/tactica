'use strict';

import { define } from 'mnemonica';

export const Main = define('Main', function (
	this: { extensionVersion: string; createdAt: number },
	extensionVersion: string
) {
	this.extensionVersion = extensionVersion;
	this.createdAt = Date.now();
});

export const Adapter = Main.define('Adapter', function (
	this: { name: string; domain: string; enabled: boolean; createdAt: number },
	data: { name: string; domain: string; enabled: boolean }
) {
	this.name = data.name;
	this.domain = data.domain;
	this.enabled = data.enabled;
	this.createdAt = Date.now();
});

export default Main;
