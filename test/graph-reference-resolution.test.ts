'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as ts from 'typescript';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { run } from '../src/cli';
import { TypesGenerator } from '../src/generator';

/**
 * Compile generated files with a real ts.Program (mnemonica paths-mapped,
 * mirroring the generator TS2300 test) and return the error list — empty
 * means the generated output is valid TypeScript.
 */
const compileGeneratedTypes = (files: string[], baseUrl: string): string[] => {
	const mnemonicaTypes = path.join(__dirname, '..', 'node_modules', 'mnemonica', 'build', 'index.d.ts');
	const program = ts.createProgram(files, {
		strict           : true,
		noEmit           : true,
		target           : ts.ScriptTarget.ES2020,
		module           : ts.ModuleKind.ES2020,
		moduleResolution : ts.ModuleResolutionKind.Bundler,
		baseUrl,
		paths            : { mnemonica : [ mnemonicaTypes ] },
	});
	const errors = ts.getPreEmitDiagnostics(program)
		.filter(d => d.category === ts.DiagnosticCategory.Error)
		.map(d => `TS${d.code}: ${ts.flattenDiagnosticMessageText(d.messageText, ' ')}`);
	const result = errors;
	return result;
};

interface HierarchyNode {
	fullPath: string;
	children: HierarchyNode[];
}

/**
 * Graph identity law (F10 follow-up): references to mnemonica graph types
 * resolve path-aware — relative-first up the anchor's parent chain, then
 * the anchor's collection roots, then a program-wide search that must be
 * unique. File-local value bindings and import anchors disambiguate first.
 * Same-namespace duplicate definitions (ALREADY_DECLARED at runtime) and
 * graph references that stay ambiguous or unresolved are fatal: the CLI
 * prints every location, exits non-zero, and writes no .tactica output.
 */
describe('Graph identity law (F10 follow-up)', () => {

	describe('construction shapes beyond plain new (chain / fork / call)', () => {
		const analyzeShapes = (body: string): MnemonicaAnalyzer => {
			const analyzer = new MnemonicaAnalyzer();
			analyzer.analyzeSource(`
import { define, call, apply, bind, utils } from 'mnemonica';

const LedgerRoot = define('LedgerRoot', function (this: LedgerRoot) {
	this.kind = 'root';
});
LedgerRoot.define('SettleBatch', function (this: SettleBatch, data: { batch: string }) {
	this.batch = data.batch;
});

${body}
`, path.join(__dirname, 'fixtures', 'graph-shapes', 'src', 'unit-inline.ts'));
			return analyzer;
		};

		it('records the chain tip as an instantiation and binds the result var to the tip (sync + await)', () => {
			const analyzer = analyzeShapes(`
async function run () {
	const chained = await new LedgerRoot().SettleBatch({ batch: 'b1' });
	const chainedSync = new LedgerRoot().SettleBatch({ batch: 'b2' });
	return [ chained, chainedSync ];
}

const chainedAtModule = new LedgerRoot().SettleBatch({ batch: 'm' });
export const ChainHolder = define('ChainHolder', function (this: ChainHolder) {
	this.chained = chainedAtModule;
});
`);
			const tipUsages = analyzer.getUsages().get('LedgerRoot.SettleBatch');
			expect(tipUsages).to.exist;
			expect(tipUsages!.filter(u => u.kind === 'instantiation')).to.have.length(3);
			expect(tipUsages![ 0 ].constructorText).to.include('SettleBatch');

			// the result variable holds the TIP's type, not the root's —
			// surfaced through the value-scope binding on the assignment
			const holder = analyzer.getGraph().findType('ChainHolder');
			expect(holder).to.exist;
			expect(holder!.properties.get('chained')?.type).to.equal('LedgerRoot_SettleBatch');
		});

		it('records fork/clone/merge as instantiations (owner decision: construction re-runs), keeping bindings and flow', () => {
			const analyzer = analyzeShapes(`
const entry = new LedgerRoot({ code: 'a' });
const forkedFresh = entry.fork({ code: 'b' });
const forkedPlain = entry.fork();
const clonedProp = entry.clone;
const clonedCall = entry.clone();
const merged = utils.merge(entry, { extra: true });
const curried = utils.fork(entry)({ code: 'c' });
const awaitedFork = await entry.fork({ code: 'd' });

export const ForkSurface = define('ForkSurface', function (this: ForkSurface) {
	this.fresh = forkedFresh;
	this.merged = merged;
});
`);
			const usages = analyzer.getUsages().get('LedgerRoot');
			expect(usages).to.exist;
			const constructions = usages!.filter(u => u.kind === 'instantiation');
			// new + fork×3 (fresh, plain, awaited) + clone×2 + merge +
			// curried inner-line + curried invocation
			expect(constructions).to.have.length(9);
			expect(constructions.filter(u => u.constructorText === 'entry.fork')).to.have.length(3);
			expect(constructions.filter(u => u.constructorText === 'entry.clone')).to.have.length(2);
			expect(constructions.filter(u => u.constructorText === 'utils.merge')).to.have.length(1);
			expect(constructions.filter(u => u.constructorText?.startsWith('utils.fork'))).to.have.length(2);

			// the generic methodCall flow entries stay (movement)
			const flow = analyzer.getFlowUsages().get('LedgerRoot') ?? [];
			expect(flow.filter(f => f.kind === 'methodCall' && f.propertyName === 'fork')).to.have.length(3);
			expect(flow.filter(f => f.kind === 'propertyRead' && f.propertyName === 'clone')).to.have.length(2);

			// result bindings stay intact, surfaced through the later define
			const surface = analyzer.getGraph().findType('ForkSurface');
			expect(surface!.properties.get('fresh')?.type).to.equal('LedgerRoot');
			expect(surface!.properties.get('merged')?.type).to.equal('LedgerRoot');
		});

		it('binds fork/clone results to the source type', () => {
			const analyzer = analyzeShapes(`
const entry = new LedgerRoot();
const forked = entry.fork({ kind: 'again' });
const cloned = entry.clone();
export const ShapeHolder = define('ShapeHolder', function (this: ShapeHolder) {
	this.forked = forked;
	this.cloned = cloned;
});
`);
			const holder = analyzer.getGraph().findType('ShapeHolder');
			expect(holder).to.exist;
			expect(holder!.properties.get('forked')?.type).to.equal('LedgerRoot');
			expect(holder!.properties.get('cloned')?.type).to.equal('LedgerRoot');
		});

		it('binds utils.merge / curried utils.fork results to arg 0\'s type', () => {
			const analyzer = analyzeShapes(`
const entry = new LedgerRoot();
const merged = utils.merge(entry, { extra: true });
const curried = utils.fork(entry)({ kind: 'forked' });
export const UtilHolder = define('UtilHolder', function (this: UtilHolder) {
	this.merged = merged;
	this.curried = curried;
});
`);
			const holder = analyzer.getGraph().findType('UtilHolder');
			expect(holder).to.exist;
			expect(holder!.properties.get('merged')?.type).to.equal('LedgerRoot');
			expect(holder!.properties.get('curried')?.type).to.equal('LedgerRoot');
		});

		it('treats mnemonica call/apply as construction of the Ctor arg and binds bind() results', () => {
			const analyzer = analyzeShapes(`
const entry = new LedgerRoot();
const viaCall = call(entry, LedgerRoot, { kind: 'c' });
const viaApply = apply(entry, LedgerRoot, [ { kind: 'd' } ]);
const bound = bind(entry, LedgerRoot);
export const FnHolder = define('FnHolder', function (this: FnHolder) {
	this.viaCall = viaCall;
	this.viaApply = viaApply;
	this.bound = bound;
});
`);
			const usages = analyzer.getUsages().get('LedgerRoot');
			expect(usages).to.exist;
			const constructions = usages!.filter(u => u.kind === 'instantiation');
			// new + call + apply — bind() records NO usage (it constructs
			// nothing; it only binds the result variable)
			expect(constructions).to.have.length(3);
			expect(constructions.some(u => u.code.startsWith('call(') && u.constructorText === 'LedgerRoot')).to.be.true;
			expect(constructions.some(u => u.code.startsWith('apply('))).to.be.true;
			expect(constructions.some(u => u.code.startsWith('bind('))).to.be.false;

			const holder = analyzer.getGraph().findType('FnHolder');
			expect(holder!.properties.get('viaCall')?.type).to.equal('LedgerRoot');
			expect(holder!.properties.get('viaApply')?.type).to.equal('LedgerRoot');
			expect(holder!.properties.get('bound')?.type).to.equal('LedgerRoot');
		});

		it('is await-transparent across call/apply/bind and fork/clone', () => {
			const analyzer = analyzeShapes(`
const entry = new LedgerRoot({ code: 'a' });

async function run () {
	const viaAwaitCall = await call(entry, LedgerRoot, { code: 'b' });
	const viaAwaitApply = await apply(entry, LedgerRoot, [ { code: 'c' } ]);
	const boundFn = await bind(entry, LedgerRoot);
	const viaAwaitFork = await entry.fork({ code: 'd' });
	return [ viaAwaitCall, viaAwaitApply, boundFn, viaAwaitFork ];
}

const forkedGlobal = await entry.fork({ code: 'g' });
const clonedGlobal = entry.clone;
export const AwaitHolder = define('AwaitHolder', function (this: AwaitHolder) {
	this.forked = forkedGlobal;
	this.cloned = clonedGlobal;
});
`);
			const usages = analyzer.getUsages().get('LedgerRoot');
			const constructions = usages?.filter(u => u.kind === 'instantiation') ?? [];
			expect(constructions.filter(u => u.code.startsWith('call('))).to.have.length(1);
			expect(constructions.filter(u => u.code.startsWith('apply('))).to.have.length(1);

			const holder = analyzer.getGraph().findType('AwaitHolder');
			expect(holder!.properties.get('forked')?.type).to.equal('LedgerRoot');
			expect(holder!.properties.get('cloned')?.type).to.equal('LedgerRoot');
		});

		it('resolves a @decorate()-ed class as the Ctor; a plain class binds nothing', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzer.analyzeSource(`
import { define, decorate, call } from 'mnemonica';

const LedgerRoot = define('LedgerRoot', function (this: LedgerRoot) {
	this.kind = 'root';
});

@decorate()
class DecoratedEntry {
	label: string;
	constructor (label: string) {
		this.label = label;
	}
}

class PlainEntry {
	label: string;
	constructor (label: string) {
		this.label = label;
	}
}

async function run (entry: any) {
	const viaDecorated = await call(entry, DecoratedEntry, 'x');
	const viaPlain = await call(entry, PlainEntry, 'y');
	return [ viaDecorated, viaPlain ];
}
`, path.join(__dirname, 'fixtures', 'graph-shapes', 'src', 'unit-inline.ts'));

			const usages = analyzer.getUsages().get('DecoratedEntry');
			expect(usages).to.exist;
			const constructions = usages!.filter(u => u.kind === 'instantiation');
			expect(constructions).to.have.length(1);
			expect(constructions[ 0 ].constructorText).to.equal('DecoratedEntry');

			// the plain class has no graph entry: no usage, no binding —
			// never a bare name (documented boundary)
			expect(analyzer.getUsages().get('PlainEntry')).to.be.undefined;
		});

		it('never matches userland call/apply functions (import-awareness)', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzer.analyzeSource(`
import { define } from 'mnemonica';

function call (entity: object, fn: object) {
	return fn;
}

const LedgerRoot = define('LedgerRoot', function (this: LedgerRoot) {
	this.kind = 'root';
});

export const Sneaky = define('Sneaky', function (this: Sneaky) {
	const entry = new LedgerRoot();
	const notConstruction = call(entry, LedgerRoot);
	this.result = notConstruction;
});
`, path.join(__dirname, 'fixtures', 'graph-shapes', 'src', 'unit-inline.ts'));

			const usages = analyzer.getUsages().get('LedgerRoot');
			const constructions = usages?.filter(u => u.kind === 'instantiation') ?? [];
			expect(constructions.filter(u => u.code.startsWith('call('))).to.have.length(0);
			// the userland call binds nothing: the assignment stays unknown
			const sneaky = analyzer.getGraph().findType('Sneaky');
			expect(sneaky!.properties.get('result')?.type).to.equal('unknown');
		});
	});

	describe('path-aware resolution in the analyzer', () => {
		it('resolves same-named subtypes relative-first: each Order gets its own Leaf', () => {
			const analyzer = new MnemonicaAnalyzer();
			const file = path.join(__dirname, 'fixtures', 'graph-anchored', 'src', 'unit-inline.ts');
			analyzer.analyzeSource(`
import { define } from 'mnemonica';

export const Alpha = define('Alpha', function (this: Alpha) {
	this.tone = 'a';
});
export const Gamma = define('Gamma', function (this: Gamma) {
	this.shade = 'g';
});
Alpha.define('Leaf', function (this: Leaf, data: { tone: string }) {
	this.tone = data.tone;
});
Gamma.define('Leaf', function (this: Leaf, data: { shade: string }) {
	this.shade = data.shade;
});
Alpha.define('Order', function (this: Order, data: Leaf) {
	this.leaf = data;
});
Gamma.define('Order', function (this: Order, data: Leaf) {
	this.leaf = data;
});
`, file);

			const generator = new TypesGenerator(analyzer.getGraph());
			const generated = generator.generateTypesFile();

			// the old first-match scan emitted Alpha_Leaf for both Orders
			expect(generated.content).to.include('leaf: Alpha_Leaf');
			expect(generated.content).to.include('leaf: Gamma_Leaf');
			expect(generated.content.split('leaf: Alpha_Leaf').length - 1).to.equal(1);
			// every reference resolved — nothing is fatal
			expect(analyzer.getResolutionErrors()).to.deep.equal([]);
		});
	});

	describe('lookup() path validation', () => {
		it('hard-fails an unresolved lookup with did-you-mean candidates', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzer.analyzeSource(`
import { define, lookup } from 'mnemonica';

const Holder = define('Holder', function (this: Holder) {});
Holder.define('Token', function (this: Token, data: { mark: string }) {
	this.mark = data.mark;
});
const Other = define('Other', function (this: Other) {});
Other.define('Token', function (this: Token, data: { hue: string }) {
	this.hue = data.hue;
});
const TokenCtor = lookup('Token');
new TokenCtor({ mark: 'x' });
`, path.join(__dirname, 'fixtures', 'graph-lookup-ambiguous', 'src', 'unit-inline.ts'));

			const errors = analyzer.getResolutionErrors();
			expect(errors).to.have.length(1);
			expect(errors[ 0 ].message).to.include('Unresolved lookup of mnemonica type \'Token\'');
			expect(errors[ 0 ].message).to.include('Holder.Token');
			expect(errors[ 0 ].message).to.include('Other.Token');
			// idempotent: a second call must not double-record
			expect(analyzer.getResolutionErrors()).to.have.length(1);
		});

		it('hard-fails a lookup matching nothing, without candidates', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzer.analyzeSource(`
import { define, lookup } from 'mnemonica';

const Holder = define('Holder', function (this: Holder) {});
const Ghost = lookup('Ghost');
`, path.join(__dirname, 'fixtures', 'graph-lookup-ambiguous', 'src', 'unit-inline.ts'));

			const errors = analyzer.getResolutionErrors();
			expect(errors).to.have.length(1);
			expect(errors[ 0 ].message).to.include('no type at that path');
		});

		it('accepts dotted and receiver-relative lookups', () => {
			const analyzer = new MnemonicaAnalyzer();
			analyzer.analyzeSource(`
import { define, lookup } from 'mnemonica';

const Holder = define('Holder', function (this: Holder) {});
Holder.define('Token', function (this: Token, data: { mark: string }) {
	this.mark = data.mark;
});
const ByPath = lookup('Holder.Token');
const ByReceiver = Holder.lookup('Token');
new ByPath({ mark: 'x' });
new ByReceiver({ mark: 'y' });
`, path.join(__dirname, 'fixtures', 'graph-lookup-valid', 'src', 'unit-inline.ts'));

			expect(analyzer.getResolutionErrors()).to.deep.equal([]);
		});
	});

	describe('CLI hard-fail', () => {
		const fixtureRoot = path.join(__dirname, 'fixtures');

		const runCapturingErrors = (options: Parameters<typeof run>[0]): { code: number; errors: string } => {
			const originalError = console.error;
			let captured = '';
			console.error = (...args: unknown[]): void => {
				captured += `${args.map(String).join(' ')  }\n`;
			};
			let code = 0;
			try {
				code = run(options);
			} finally {
				console.error = originalError;
			}
			const result = { code, errors : captured };
			return result;
		};

		it('resolves an import-anchored reference and exits 0', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-graph-anchored-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-anchored', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');
				const types = fs.readFileSync(path.join(outputDir, 'types.ts'), 'utf8');
				expect(types).to.include('item: Holder_Token');
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('hard-fails on an ambiguous graph reference and writes no output', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-graph-ambiguous-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-ambiguous', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(1);
				expect(errors).to.include('Ambiguous reference');
				expect(errors).to.include('Token');
				// the whole point of the hard fail: no partial output
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.false;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('hard-fails on an unresolved lookup path and writes no output', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-lookup-ambiguous-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-lookup-ambiguous', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(1);
				expect(errors).to.include('Unresolved lookup');
				expect(errors).to.include('Token');
				expect(errors).to.include('Holder.Token');
				expect(errors).to.include('would return undefined');
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.false;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('accepts dotted and receiver-relative lookups and exits 0', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-lookup-valid-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-lookup-valid', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.true;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('hard-fails on an ambiguous plain-TS reference and writes no output', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-plaints-duplicates-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'plaints-duplicates', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(1);
				expect(errors).to.include('Ambiguous reference to type \'SharedShape\'');
				expect(errors).to.include('no import disambiguates');
				expect(errors).to.include('import the one you mean');
				// the reference site plus EVERY declaration site
				expect(errors).to.include(path.join('src', 'consumer.ts'));
				expect(errors).to.include(path.join('src', 'a.ts'));
				expect(errors).to.include(path.join('src', 'b.ts'));
				// the whole point of the hard fail: no partial output
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.false;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('resolves an import-anchored plain-TS duplicate and exits 0', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-plaints-anchored-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'plaints-anchored', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');
				const types = fs.readFileSync(path.join(outputDir, 'types.ts'), 'utf8');
				expect(types).to.include('item: { a: string }');
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});

		it('binds a multi-hop const chain to the LAST hop and keeps root arg fields in nested types (F18, F19 law)', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-const-chain-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'const-chain', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');

				const hierarchy = JSON.parse(
					fs.readFileSync(path.join(outputDir, 'hierarchy.json'), 'utf8')
				) as { roots: HierarchyNode[] };
				const paths: string[] = [];
				const walk = (nodes: HierarchyNode[]): void => {
					for (const node of nodes) {
						paths.push(node.fullPath);
						walk(node.children);
					}
				};
				walk(hierarchy.roots);

				// F18: Branch bound the last hop (TrunkRoot.Limb.Joint), so
				// its child lands under Joint — the old first-hop binding
				// misplaced it under Limb
				expect(paths).to.include('TrunkRoot.Limb.Joint.Tip');
				expect(paths).to.not.include('TrunkRoot.Limb.Tip');
				expect(paths).to.include('TrunkRoot.Limb.Joint');
				// single-hop control: the const binds the only hop
				expect(paths).to.include('TrunkRoot.Solo.Cap');

				// F19 law pin: the root's own arg fields reach nested
				// instance types through the ProtoFlat chain — direct child
				// and deeper levels alike (compiles only while true)
				const assertionsPath = path.join(outputDir, 'field-assertions.ts');
				fs.writeFileSync(assertionsPath, [
					'import type { PaymentRoot, PaymentRoot_GatheredContext, PaymentRoot_GatheredContext_DeepLeaf } from \'./types\';',
					'',
					'const deep = {} as PaymentRoot_GatheredContext_DeepLeaf;',
					'const uuidDeep: string = deep.uuid;',
					'const gatheredDeep: string = deep.gathered;',
					'const leafDeep: string = deep.leaf;',
					'const mid = {} as PaymentRoot_GatheredContext;',
					'const uuidMid: string = mid.uuid;',
					'const root = {} as PaymentRoot;',
					'const uuidRoot: string = root.uuid;',
					'void [ uuidDeep, gatheredDeep, leafDeep, uuidMid, uuidRoot ];',
					'',
				].join('\n'));

				const compileErrors = compileGeneratedTypes(
					[ path.join(outputDir, 'types.ts'), assertionsPath ],
					outputDir
				);
				expect(compileErrors).to.deep.equal([]);
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		}).timeout(20000);

		it('tolerates the self-referencing root ctor annotation and stays assignable (pattern pin)', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-self-alias-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'self-alias', 'tsconfig.json'),
					outputDir,
				});

				// (a) regeneration is clean
				expect(code).to.equal(0);
				expect(errors).to.equal('');

				const typesPath = path.join(outputDir, 'types.ts');
				const content = fs.readFileSync(typesPath, 'utf8');

				// (b) no circularity: the alias never lands in the emitted
				// type, which carries plain extracted properties only
				expect(content).to.include('export type Widget = {');
				expect(content).to.include('label: string;');
				expect(content).to.include('size: number;');
				expect(content).to.not.include('TWidgetInstance');

				// (c) call-site assignability: the typed lookup constructor
				// returns the generated instance type directly
				const callsitePath = path.join(outputDir, 'callsite.ts');
				fs.writeFileSync(callsitePath, [
					'import { lookup } from \'mnemonica\';',
					'import \'./registry\';',
					'import type { Widget } from \'./types\';',
					'',
					'const Ctor = lookup(\'Widget\');',
					'const w: Widget = new Ctor({ label: \'x\', size: 3 });',
					'const expected: { label: string; size: number } = w;',
					'void expected;',
					'',
				].join('\n'));

				const compileErrors = compileGeneratedTypes(
					[ typesPath, path.join(outputDir, 'registry.ts'), callsitePath ],
					outputDir
				);
				expect(compileErrors).to.deep.equal([]);
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		}).timeout(20000);

		it('keeps a root-level child of an intersection-alias root seeing the root arg fields (F21)', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-self-alias-intersection-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'self-alias-intersection', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(0);
				expect(errors).to.equal('');

				const typesPath = path.join(outputDir, 'types.ts');
				const content = fs.readFileSync(typesPath, 'utf8');

				// the root's own arg fields are extracted from the
				// Object.assign(this, args) identifier form — the
				// intersection this-alias is ergonomic-only and its members
				// are never expanded
				expect(content).to.include('code: string;');
				expect(content).to.include('amount: number;');
				expect(content).to.include('export type VaultRoot_FailedUnlock = ProtoFlat<VaultRoot, {');
				expect(content).to.not.include('TVaultInstance');
				expect(content).to.not.include('TEntryArgs');

				// the consumer contract: a root-level child statically sees
				// the root's arg fields (compiles only while true)
				const assertionsPath = path.join(outputDir, 'field-assertions.ts');
				fs.writeFileSync(assertionsPath, [
					'import type { VaultRoot_FailedUnlock } from \'./types\';',
					'',
					'const attempt = {} as VaultRoot_FailedUnlock;',
					'const code: string = attempt.code;',
					'const amount: number = attempt.amount;',
					'const reason: string = attempt.reason;',
					'void [ code, amount, reason ];',
					'',
				].join('\n'));

				const compileErrors = compileGeneratedTypes(
					[ typesPath, assertionsPath ],
					outputDir
				);
				expect(compileErrors).to.deep.equal([]);
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		}).timeout(20000);

		it('hard-fails on same-namespace duplicates, reporting every site', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-graph-duplicates-'));
			try {
				const { code, errors } = runCapturingErrors({
					project : path.join(fixtureRoot, 'graph-duplicates', 'tsconfig.json'),
					outputDir,
				});

				expect(code).to.equal(1);
				expect(errors).to.include('Duplicate definition');
				expect(errors).to.include('ALREADY_DECLARED');
				expect(errors).to.include(path.join('src', 'dup-a.ts'));
				expect(errors).to.include(path.join('src', 'dup-b.ts'));
				expect(errors).to.include('Twin');
				expect(fs.existsSync(path.join(outputDir, 'types.ts'))).to.be.false;
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});
	});
});
