'use strict';

// Plugin module loaded by string specifier from .tactica.js — the same
// form an adapter package's plugin subpath takes from a project config.
const fixturePlugin = {
	name                      : 'fixture-string',
	instrumentationInterfaces : {
		FixtureGuardInterface : 'guard',
	},
};

module.exports = fixturePlugin;
