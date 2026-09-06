'use strict';

import { expect } from 'chai';
import { mergeTacticaPlugins, TacticaPlugin } from '../src/plugins';

describe('mergeTacticaPlugins()', () => {
	it('should return an empty vocabulary for no plugins', () => {
		const merged = mergeTacticaPlugins([]);
		expect(merged).to.deep.equal({
			interfaces       : {},
			useDecorators    : {},
			appTokens        : {},
			middlewareWiring : false,
		});
	});

	it('should merge vocabulary maps across plugins', () => {
		const plugins: TacticaPlugin[] = [
			{
				name                      : 'first',
				instrumentationInterfaces : { AlphaInterceptor : 'interceptor' },
				useDecorators             : { UseAlpha : 'interceptor' },
			},
			{
				name                      : 'second',
				instrumentationInterfaces : { BetaGuard : 'guard' },
				appTokens                 : { BETA_TOKEN : 'guard' },
			},
		];

		const merged = mergeTacticaPlugins(plugins);
		expect(merged.interfaces).to.deep.equal({
			AlphaInterceptor : 'interceptor',
			BetaGuard        : 'guard',
		});
		expect(merged.useDecorators).to.deep.equal({ UseAlpha : 'interceptor' });
		expect(merged.appTokens).to.deep.equal({ BETA_TOKEN : 'guard' });
		expect(merged.middlewareWiring).to.be.false;
	});

	it('should let later plugins override earlier ones on the same key', () => {
		const merged = mergeTacticaPlugins([
			{ instrumentationInterfaces : { SharedName : 'guard' } },
			{ instrumentationInterfaces : { SharedName : 'filter' } },
		]);
		expect(merged.interfaces).to.deep.equal({ SharedName : 'filter' });
	});

	it('should treat middlewareWiring as an OR across plugins', () => {
		const merged = mergeTacticaPlugins([
			{ name : 'a' },
			{ name : 'b', middlewareWiring : true },
			{ name : 'c' },
		]);
		expect(merged.middlewareWiring).to.be.true;
	});

	it('should not mutate the given plugin objects', () => {
		const plugin: TacticaPlugin = {
			instrumentationInterfaces : { AlphaInterceptor : 'interceptor' },
		};
		mergeTacticaPlugins([ plugin, { instrumentationInterfaces : { BetaGuard : 'guard' } } ]);
		expect(plugin.instrumentationInterfaces).to.deep.equal({ AlphaInterceptor : 'interceptor' });
	});
});
