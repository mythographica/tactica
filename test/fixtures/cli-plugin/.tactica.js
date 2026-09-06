'use strict';

// tactica project config: plugins supply the framework instrumentation
// vocabulary. String entries are module specifiers required relative to
// THIS file; inline objects cover the object form. Both merge.
module.exports = {
	plugins : [
		'./fixture-plugin.js',
		{
			name                      : 'fixture-inline',
			instrumentationInterfaces : {
				InlineGuardInterface : 'guard',
			},
			appTokens : {
				FIXTURE_TOKEN : 'guard',
			},
		},
	],
};
