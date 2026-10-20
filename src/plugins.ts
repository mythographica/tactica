'use strict';

import { InstrumentationKind } from './types';

/**
 * Tactica plugin: supplies the framework vocabulary the analyzer matches
 * syntactically. Tactica core is framework-blind — with no plugins loaded
 * it detects no instrumentation points at all. Framework adapters (e.g. a
 * server-framework integration package) ship a plugin; projects enable it
 * through a `.tactica.js` / `tactica.config.js` config file.
 *
 * All keys are matched by identifier TEXT only (no import resolution, no
 * type checker), so a plugin entry fires on any same-named identifier.
 */
/**
 * One decorator-arg factory entry: the instrumentation kind, the target
 * argument position (default 0), and whether the factory constructs the
 * target type on the caller's behalf (`instantiation`).
 */
export interface DecoratorArgFactory {
	kind: InstrumentationKind;
	targetArg?: number;
	/**
	 * The factory constructs the type passed at `targetArg` (e.g. a pipe
	 * that runs `new Target(body)` per request): each matched call whose
	 * target resolves to a defined type is recorded in usages.json and
	 * flow.json as an `instantiation` of that type at the call site.
	 */
	instantiation?: boolean;
}

export interface TacticaPlugin {
	/** Plugin name, used in verbose logging */
	name?: string;
	/** Heritage interface identifier -> kind (`implements X`) */
	instrumentationInterfaces?: Record<string, InstrumentationKind>;
	/** Decorator identifier -> kind (`@X(Impl)` on classes/methods) */
	useDecorators?: Record<string, InstrumentationKind>;
	/** Provider token identifier -> kind (`{ provide: TOKEN, useClass: X }`) */
	appTokens?: Record<string, InstrumentationKind>;
	/**
	 * Decorator-arg factory method -> kind + target argument position
	 * (`@UsePipes(mvp.forType(Dto))`): a CallExpression arg whose callee is
	 * `<anything>.<name>(...)` matches when `name` is listed; the point's
	 * class is the identifier in `targetArg` (default 0). With
	 * `instantiation: true` the call is also a construction of that type.
	 */
	decoratorArgFactories?: Record<string, DecoratorArgFactory>;
	/**
	 * Enable middleware wiring detection: `consumer.apply(Mw).forRoutes(...)`
	 * inside a `configure()` method. Shape-based (no vocabulary keys), so it
	 * is opt-in per plugin.
	 */
	middlewareWiring?: boolean;
}

/**
 * The analyzer's merged view of all loaded plugins: one lookup table per
 * detection channel, plus the middleware-wiring switch.
 */
export interface InstrumentationVocabulary {
	interfaces: Record<string, InstrumentationKind>;
	useDecorators: Record<string, InstrumentationKind>;
	appTokens: Record<string, InstrumentationKind>;
	decoratorArgFactories: Record<string, DecoratorArgFactory>;
	middlewareWiring: boolean;
}

/**
 * Merge plugins into one vocabulary. Later plugins override earlier ones on
 * the same identifier key; middlewareWiring is an OR (any plugin enables it).
 * An empty plugin list yields an empty vocabulary — the analyzer then
 * collects zero instrumentation points.
 */
export function mergeTacticaPlugins (plugins: TacticaPlugin[]): InstrumentationVocabulary {
	const merged: InstrumentationVocabulary = {
		interfaces            : {},
		useDecorators         : {},
		appTokens             : {},
		decoratorArgFactories : {},
		middlewareWiring      : false,
	};
	for (const plugin of plugins) {
		Object.assign(merged.interfaces, plugin.instrumentationInterfaces);
		Object.assign(merged.useDecorators, plugin.useDecorators);
		Object.assign(merged.appTokens, plugin.appTokens);
		Object.assign(merged.decoratorArgFactories, plugin.decoratorArgFactories);
		if (plugin.middlewareWiring) {
			merged.middlewareWiring = true;
		}
	}
	return merged;
}
