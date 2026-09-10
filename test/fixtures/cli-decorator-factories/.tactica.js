'use strict';

// tactica project config: inline plugin object exercising the
// decoratorArgFactories channel (pipe-factory calls in decorator args)
module.exports = {
	plugins : [
		{
			name          : 'fixture-factories',
			useDecorators : {
				UsePipes  : 'pipe',
				UseGuards : 'guard',
				Body      : 'pipe',
			},
			decoratorArgFactories : {
				forType   : { kind : 'pipe', targetArg : 0 },
				bindGuard : { kind : 'guard', targetArg : 1 },
			},
		},
	],
};
