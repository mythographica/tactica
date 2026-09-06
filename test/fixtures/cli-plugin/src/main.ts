// Fixture source for the CLI plugin test. The identifiers below mean
// nothing to tactica core — the project's .tactica.js config supplies the
// vocabulary through two plugins: one loaded by string specifier, one
// inline.

export class FixtureGuard implements FixtureGuardInterface {
	canActivate () {
		return true;
	}
}

export class InlineGuard implements InlineGuardInterface {
	canActivate () {
		return true;
	}
}

const providers = [
	{ provide : FIXTURE_TOKEN, useClass : FixtureGuard },
];
void providers;
