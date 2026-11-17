import { expect } from 'chai';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { run } from '../src/cli';
import type { UsageInfo } from '../src/types';

/**
 * Usages land on the type really constructed: a construction through a
 * receiver tactica cannot bind by value is attributed by the receiver's
 * declared type, or to every namesake — never to the first namesake
 * only; a bare `instance.Sub(…)` call is a construction; one record per
 * site.
 */
describe('Usage attribution', () => {
	const twoFlows = `
		import { define } from 'mnemonica';
		const Alpha = define('Alpha', function () {});
		const AlphaGadget = Alpha.define('Gadget', function () {});
		AlphaGadget.define('Fault', function () {});
		AlphaGadget.define('Done', function () {});
		const Beta = define('Beta', function () {});
		const BetaGadget = Beta.define('Gadget', function () {});
		BetaGadget.define('Fault', function () {});
		BetaGadget.define('Done', function () {});
	`;

	const analyze = (body: string): MnemonicaAnalyzer => {
		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(`${twoFlows}\n${body}`);
		const result = analyzer;
		return result;
	};

	const kindsOf = (analyzer: MnemonicaAnalyzer, typePath: string): string[] => {
		const usages: UsageInfo[] = analyzer.getUsages().get(typePath) || [];
		const kinds = usages.map(usage => usage.kind);
		return kinds;
	};

	describe('a receiver typed by its annotation', () => {
		it('attributes a construction to every member of a union of generated types', () => {
			const analyzer = analyze(`
				type AnyGadget = Alpha_Gadget | Beta_Gadget;
				const makeFault = function (gadget: AnyGadget) {
					const fault = new gadget.Fault();
					return fault;
				};
			`);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
		});

		it('attributes a construction to the one generated type an annotation names', () => {
			const analyzer = analyze(`
				const makeFault = function (gadget: Beta_Gadget) {
					const fault = new gadget.Fault();
					return fault;
				};
			`);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([]);
		});

		it('follows intersections, parentheses and interface extends', () => {
			const analyzer = analyze(`
				interface BetaLike extends Beta_Gadget {}
				const viaIntersection = function (gadget: { extra: number } & (Alpha_Gadget)) {
					const done = new gadget.Done();
					return done;
				};
				const viaInterface = function (gadget: BetaLike) {
					const done = new gadget.Done();
					return done;
				};
			`);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Done')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Beta.Gadget.Done')).to.deep.equal([ 'instantiation' ]);
		});

		it('reads an annotated const in an enclosing block', () => {
			const analyzer = analyze(`
				const build = function (pick: () => Beta_Gadget) {
					const gadget: Beta_Gadget = pick();
					const fault = new gadget.Fault();
					return fault;
				};
			`);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([]);
		});
	});

	describe('a receiver tactica cannot bind', () => {
		it('attributes a structural parent to every namesake, not the first', () => {
			const analyzer = analyze(`
				type HasDone = { Done: new () => { d: number } };
				const makeDone = function (gadget: HasDone) {
					const done = new gadget.Done();
					return done;
				};
			`);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Done')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Beta.Gadget.Done')).to.deep.equal([ 'instantiation' ]);
		});

		it('attributes an unannotated parameter to every namesake, not the first', () => {
			const analyzer = analyze(`
				const makeFault = function (gadget) {
					const fault = new gadget.Fault();
					return fault;
				};
			`);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
		});

		it('attributes an undeclared receiver to every namesake', () => {
			const analyzer = analyze(`
				const fault = new undeclaredGadget.Fault();
			`);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
		});

		it('falls back to every namesake when the annotation names no generated type', () => {
			const analyzer = analyze(`
				interface Plain { x: number }
				type Loop = Again;
				type Again = Loop;
				const viaUnknownName = function (gadget: NotDeclaredAnywhere) {
					const fault = new gadget.Fault();
					return fault;
				};
				const viaPlainInterface = function (gadget: Plain) {
					const fault = new gadget.Fault();
					return fault;
				};
				const viaAliasCycle = function (gadget: Loop) {
					const done = new gadget.Done();
					return done;
				};
				const viaDeepNesting = function (gadget: ((((((((((Alpha_Gadget)))))))))) ) {
					const done = new gadget.Done();
					return done;
				};
			`);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([ 'instantiation', 'instantiation' ]);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation', 'instantiation' ]);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Done')).to.deep.equal([ 'instantiation', 'instantiation' ]);
			expect(kindsOf(analyzer, 'Beta.Gadget.Done')).to.deep.equal([ 'instantiation', 'instantiation' ]);
		});

		it('keeps a value-bound receiver on its own type', () => {
			const analyzer = analyze(`
				const beta = new Beta();
				const betaGadget = new beta.Gadget();
				const fault = new betaGadget.Fault();
			`);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([]);
		});
	});

	describe('construction without new', () => {
		it('records a bare subtype call on a bound instance as an instantiation, once', () => {
			const analyzer = analyze(`
				const beta = new Beta();
				const gadget = beta.Gadget();
				const fault = gadget.Fault();
			`);
			expect(kindsOf(analyzer, 'Beta.Gadget')).to.deep.equal([ 'instantiation' ]);
			// the result variable binds to the constructed type
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([]);
		});

		it('records a bare subtype call on an annotated parameter for every member', () => {
			const analyzer = analyze(`
				const makeFault = function (gadget: Alpha_Gadget | Beta_Gadget) {
					const fault = gadget.Fault();
					return fault;
				};
			`);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
		});

		it('records a chain tip once, as an instantiation', () => {
			const analyzer = analyze(`
				const gadget = new Beta().Gadget();
			`);
			expect(kindsOf(analyzer, 'Beta.Gadget')).to.deep.equal([ 'instantiation' ]);
			// no second record at the site, on a namesake either
			expect(kindsOf(analyzer, 'Alpha.Gadget')).to.deep.equal([]);
		});

		it('binds an awaited, parenthesized bare call to its result variable', () => {
			const analyzer = analyze(`
				const run = async function () {
					const beta = new Beta();
					const gadget = await (beta.Gadget());
					const fault = gadget.Fault();
					return fault;
				};
			`);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([]);
		});

		it('does not count a call on an unknown receiver as a construction', () => {
			const analyzer = analyze(`
				const fault = undeclaredGadget.Fault();
			`);
			expect(kindsOf(analyzer, 'Alpha.Gadget.Fault')).to.deep.equal([ 'propertyAccess' ]);
			expect(kindsOf(analyzer, 'Beta.Gadget.Fault')).to.deep.equal([ 'propertyAccess' ]);
		});

		it('records a subtype read by its full path on the type itself', () => {
			const analyzer = analyze(`
				const GadgetCtor = Beta.Gadget;
			`);
			expect(kindsOf(analyzer, 'Beta.Gadget')).to.deep.equal([ 'propertyAccess' ]);
			expect(kindsOf(analyzer, 'Alpha.Gadget')).to.deep.equal([]);
		});

		it('keeps a constructor read as a propertyAccess', () => {
			const analyzer = analyze(`
				const beta = new Beta();
				const table = { Gadget : beta.Gadget };
			`);
			expect(kindsOf(analyzer, 'Beta.Gadget')).to.deep.equal([ 'propertyAccess' ]);
		});
	});

	describe('across files (CLI run)', () => {
		it('reads an alias union of imported generated types, renamed imports included', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-usage-attribution-'));
			try {
				const code = run({
					project : path.join(__dirname, 'fixtures', 'usage-attribution', 'tsconfig.json'),
					outputDir,
				});
				expect(code).to.equal(0);
				const usagesFile = JSON.parse(fs.readFileSync(path.join(outputDir, 'usages.json'), 'utf8')) as {
					usages: Record<string, UsageInfo[]>;
				};
				const kinds = (typePath: string): string[] => {
					const list = usagesFile.usages[ typePath ] || [];
					const result = list.map(usage => usage.kind);
					return result;
				};
				expect(kinds('Alpha.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
				expect(kinds('Beta.Gadget.Fault')).to.deep.equal([ 'instantiation' ]);
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		}).timeout(20000);
	});
});
