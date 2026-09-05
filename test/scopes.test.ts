'use strict';

import { expect } from 'chai';
import * as path from 'path';
import * as ts from 'typescript';
import { LocalScopeWalker, ScopeTypeResolver } from '../src/scopes';
import { ScopeAnalysis, ScopeVariable, UsageInfo } from '../src/types';

/**
 * Local-scope walker (Phase 2 of the instrumentation walker plan).
 * Inline sources for behavior, the module-graph fixture for a real program.
 */
describe('LocalScopeWalker', () => {
	const virtualPath = (name: string): string => {
		const result = path.join('/virtual', name);
		return result;
	};

	const walkInline = (
		files: Record<string, string>,
		resolver?: ScopeTypeResolver
	): { walker: LocalScopeWalker; analysis: ScopeAnalysis } => {
		const walker = new LocalScopeWalker();
		for (const [ name, code ] of Object.entries(files)) {
			const sourceFile = ts.createSourceFile(virtualPath(name), code, ts.ScriptTarget.Latest, true);
			walker.addFile(sourceFile);
		}
		const analysis = walker.build(resolver);
		return { walker, analysis };
	};

	const variablesOf = (analysis: ScopeAnalysis, scopeId: string): ScopeVariable[] => {
		const result = Array.from(analysis.variables.values()).filter(v => v.scopeId === scopeId);
		return result;
	};

	describe('scope tracking (function/method/arrow only, no block scopes)', () => {
		// Line numbers in assertions below are 1-based in source order
		const code = [
			'function topLevel (): number {',
			'\treturn 1;',
			'}',
			'',
			'class Service {',
			'\trun (): void {',
			'\t\tconst onDone = (): void => {',
			'\t\t\tif (true) {',
			'\t\t\t\tconst inner = 1;',
			'\t\t\t\tvoid inner;',
			'\t\t\t}',
			'\t\t};',
			'\t\tonDone();',
			'\t}',
			'}',
			'',
			'setTimeout(() => {',
			'\tvoid 0;',
			'});',
			'',
		].join('\n');

		const { analysis } = walkInline({ 'scopes.ts' : code });
		const filePath = virtualPath('scopes.ts');

		it('should create a module scope per file', () => {
			const moduleScope = analysis.scopes.get(filePath);
			expect(moduleScope).to.exist;
			expect(moduleScope?.kind).to.equal('module');
			expect(moduleScope?.parentScopeId).to.equal(undefined);
		});

		it('should track named function scopes parented to the module', () => {
			const scope = analysis.scopes.get(`${filePath}:1:1`);
			expect(scope).to.exist;
			expect(scope?.kind).to.equal('function');
			expect(scope?.name).to.equal('topLevel');
			expect(scope?.parentScopeId).to.equal(filePath);
		});

		it('should label methods as Class.method', () => {
			const scope = analysis.scopes.get(`${filePath}:6:2`);
			expect(scope).to.exist;
			expect(scope?.kind).to.equal('method');
			expect(scope?.name).to.equal('Service.run');
		});

		it('should name arrows after the variable they are bound to', () => {
			const scope = analysis.scopes.get(`${filePath}:7:18`);
			expect(scope).to.exist;
			expect(scope?.kind).to.equal('arrow');
			expect(scope?.name).to.equal('onDone');
			expect(scope?.parentScopeId).to.equal(`${filePath}:6:2`);
		});

		it('should label anonymous holders as file:line', () => {
			const scope = analysis.scopes.get(`${filePath}:17:12`);
			expect(scope).to.exist;
			expect(scope?.kind).to.equal('arrow');
			expect(scope?.name).to.equal(`${filePath}:17`);
		});

		it('should NOT create block scopes (decision 5)', () => {
			for (const scope of analysis.scopes.values()) {
				expect(scope.kind).to.not.equal('block');
			}
			// The `if (true) {` block at line 8 is not a scope
			const blockScope = Array.from(analysis.scopes.keys()).find(id => id.startsWith(`${filePath}:8:`));
			expect(blockScope).to.not.exist;
			// Variables declared inside the block belong to the enclosing arrow
			const arrowVars = variablesOf(analysis, `${filePath}:7:18`);
			expect(arrowVars.map(v => v.name)).to.include('inner');
		});
	});

	describe('variables: isParameter / isMutable / reassignments (decision 6)', () => {
		// Line numbers in assertions below are 1-based in source order
		const code = [
			'function handle (input: string) {',
			'\tlet count = 1;',
			'\tconst fixed = 2;',
			'\tcount = 5;',
			'\tcount += 1;',
			'\tcount++;',
			'\tinput = \'x\';',
			'\tfixed.toFixed();',
			'\treturn count;',
			'}',
			'',
		].join('\n');

		const { analysis } = walkInline({ 'vars.ts' : code });
		const scopeId = `${virtualPath('vars.ts')}:1:1`;

		it('should track parameters as reassignable variables', () => {
			const input = analysis.variables.get(`${scopeId}#input`);
			expect(input).to.exist;
			expect(input?.isParameter).to.be.true;
			expect(input?.isMutable).to.be.true;
			expect(input?.inferredType).to.equal('string');
			expect(input?.reassignments).to.have.length(1);
		});

		it('should mark let bindings mutable and record every reassignment site', () => {
			const count = analysis.variables.get(`${scopeId}#count`);
			expect(count).to.exist;
			expect(count?.isParameter).to.be.false;
			expect(count?.isMutable).to.be.true;
			expect(count?.reassignments).to.have.length(3);
			expect(count?.reassignments[ 0 ]).to.equal(`${virtualPath('vars.ts')}:4:2`);
			expect(count?.reassignments[ 1 ]).to.equal(`${virtualPath('vars.ts')}:5:2`);
			expect(count?.reassignments[ 2 ]).to.equal(`${virtualPath('vars.ts')}:6:2`);
		});

		it('should mark const bindings immutable with no reassignments', () => {
			const fixed = analysis.variables.get(`${scopeId}#fixed`);
			expect(fixed).to.exist;
			expect(fixed?.isMutable).to.be.false;
			expect(fixed?.reassignments).to.deep.equal([]);
		});

		it('should record the declaration site on each variable', () => {
			const count = analysis.variables.get(`${scopeId}#count`);
			expect(count?.declaration).to.equal(`${virtualPath('vars.ts')}:2:6`);
		});
	});

	describe('property writes are not reassignments', () => {
		// holder.x = 1 (property write) must NOT count; holder = {} rebinds
		const code = [
			'function touch () {',
			'\tlet holder = {};',
			'\tholder.x = 1;',
			'\tholder = {};',
			'}',
			'',
		].join('\n');

		it('should record only the rebinding site', () => {
			const { analysis } = walkInline({ 'props.ts' : code });
			const holder = analysis.variables.get(`${virtualPath('props.ts')}:1:1#holder`);
			expect(holder?.reassignments).to.deep.equal([ `${virtualPath('props.ts')}:4:2` ]);
		});
	});

	describe('typePath resolution', () => {
		const resolver: ScopeTypeResolver = {
			resolveByName : (name: string): string | undefined => {
				const result = name === 'UserEntity' ? 'UserEntity' : undefined;
				return result;
			},
			hasPath : (fullPath: string): boolean => {
				const result = [ 'UserEntity', 'UserEntity.UserResponse' ].includes(fullPath);
				return result;
			},
		};

		const code = [
			'function boot () {',
			'\tconst user = new UserEntity({ id: \'1\' });',
			'\tconst response = new user.UserResponse({});',
			'\tconst typed: UserEntity_UserResponse = response;',
			'\tconst plain = new Map();',
			'\treturn response;',
			'}',
			'',
		].join('\n');

		const { analysis } = walkInline({ 'types.ts' : code }, resolver);
		const scopeId = `${virtualPath('types.ts')}:1:1`;

		it('should resolve `new KnownType()` to the mnemonica fullPath', () => {
			const user = analysis.variables.get(`${scopeId}#user`);
			expect(user?.typePath).to.equal('UserEntity');
		});

		it('should resolve `new instance.SubType()` through the root variable typePath', () => {
			const response = analysis.variables.get(`${scopeId}#response`);
			expect(response?.typePath).to.equal('UserEntity.UserResponse');
		});

		it('should resolve underscore annotation names to dotted fullPaths', () => {
			const typed = analysis.variables.get(`${scopeId}#typed`);
			expect(typed?.typePath).to.equal('UserEntity.UserResponse');
			expect(typed?.inferredType).to.equal('UserEntity_UserResponse');
		});

		it('should leave non-mnemonica constructors without typePath', () => {
			const plain = analysis.variables.get(`${scopeId}#plain`);
			expect(plain?.typePath).to.equal(undefined);
			expect(plain?.inferredType).to.equal('Map');
		});
	});

	describe('lookup() initializers (Phase 3)', () => {
		const resolver: ScopeTypeResolver = {
			resolveByName : (name: string): string | undefined => {
				const result = name === 'UserEntity' ? 'UserEntity' : undefined;
				return result;
			},
			hasPath : (fullPath: string): boolean => {
				const result = [ 'UserEntity', 'UserEntity.UserResponse' ].includes(fullPath);
				return result;
			},
		};

		it('should resolve a bare lookup(\'UserEntity\') to the fullPath', () => {
			const code = [
				'const Ctor = lookup(\'UserEntity\');',
				'',
			].join('\n');
			const { analysis } = walkInline({ 'lookup.ts' : code }, resolver);
			const variable = analysis.variables.get(`${virtualPath('lookup.ts')}#Ctor`);
			expect(variable?.typePath).to.equal('UserEntity');
		});

		it('should resolve receiver.lookup() relative to the receiver\'s typePath first', () => {
			const code = [
				'function boot () {',
				'\tconst user = new UserEntity({});',
				'\tconst response = user.lookup(\'UserResponse\');',
				'\treturn response;',
				'}',
				'',
			].join('\n');
			const { analysis } = walkInline({ 'lookup-relative.ts' : code }, resolver);
			const scopeId = `${virtualPath('lookup-relative.ts')}:1:1`;
			const variable = analysis.variables.get(`${scopeId}#response`);
			expect(variable?.typePath).to.equal('UserEntity.UserResponse');
		});

		it('should resolve the explicit-source form lookup(source, \'UserEntity\')', () => {
			const code = [
				'const Ctor = lookup(App, \'UserEntity\');',
				'',
			].join('\n');
			const { analysis } = walkInline({ 'lookup-source.ts' : code }, resolver);
			const variable = analysis.variables.get(`${virtualPath('lookup-source.ts')}#Ctor`);
			expect(variable?.typePath).to.equal('UserEntity');
		});

		it('should fall back to the literal path when the receiver is unknown', () => {
			const code = [
				'const Ctor = anything.lookup(\'UserEntity\');',
				'',
			].join('\n');
			const { analysis } = walkInline({ 'lookup-fallback.ts' : code }, resolver);
			const variable = analysis.variables.get(`${virtualPath('lookup-fallback.ts')}#Ctor`);
			expect(variable?.typePath).to.equal('UserEntity');
		});

		it('should skip computed (non-literal) lookup paths silently', () => {
			const code = [
				'function boot (name: string) {',
				'\tconst Ctor = lookup(name);',
				'\treturn Ctor;',
				'}',
				'',
			].join('\n');
			const { analysis } = walkInline({ 'lookup-computed.ts' : code }, resolver);
			const scopeId = `${virtualPath('lookup-computed.ts')}:1:1`;
			const variable = analysis.variables.get(`${scopeId}#Ctor`);
			expect(variable?.typePath).to.equal(undefined);
		});
	});

	describe('findHolderScopeId', () => {
		const code = [
			'function outer () {',
			'\tconst x = 1;',
			'\treturn function inner () {',
			'\t\treturn x;',
			'\t};',
			'}',
			'',
			'const top = 1;',
			'',
		].join('\n');

		const { walker, analysis } = walkInline({ 'holder.ts' : code });
		const filePath = virtualPath('holder.ts');

		it('should resolve the innermost containing scope', () => {
			const innerScopeId = `${filePath}:3:9`;
			expect(analysis.scopes.get(innerScopeId)?.name).to.equal('inner');
			expect(walker.findHolderScopeId(`${filePath}:4:3`)).to.equal(innerScopeId);
			expect(walker.findHolderScopeId(`${filePath}:2:3`)).to.equal(`${filePath}:1:1`);
		});

		it('should fall back to the module scope for top-level locations', () => {
			expect(walker.findHolderScopeId(`${filePath}:8:1`)).to.equal(filePath);
		});

		it('should return undefined for untracked files', () => {
			expect(walker.findHolderScopeId('/virtual/unknown.ts:1:1')).to.equal(undefined);
		});
	});

	describe('attachHolderScopeIds', () => {
		const code = [
			'function make () {',
			'\tconst x = new Thing();',
			'\treturn x;',
			'}',
			'',
		].join('\n');

		it('should attach holderScopeId additively and leave unknown files untouched', () => {
			const { walker } = walkInline({ 'attach.ts' : code });
			const usages = new Map<string, UsageInfo[]>([
				[ 'Thing', [
					{
						location : `${virtualPath('attach.ts')}:2:14`,
						kind     : 'instantiation',
						code     : 'new Thing()',
					},
					{
						location : '/elsewhere/file.ts:1:1',
						kind     : 'reference',
						code     : 'Thing',
					},
				] ],
			]);

			LocalScopeWalker.attachHolderScopeIds(usages, walker);

			const list = usages.get('Thing') as UsageInfo[];
			expect(list[ 0 ].holderScopeId).to.equal(`${virtualPath('attach.ts')}:1:1`);
			expect(list[ 1 ].holderScopeId).to.equal(undefined);
		});
	});

	describe('re-adding files', () => {
		it('should replace scope and variable records when the file is added again', () => {
			const walker = new LocalScopeWalker();
			const fileName = virtualPath('again.ts');

			const first = ts.createSourceFile(fileName, 'function a () {}\n', ts.ScriptTarget.Latest, true);
			walker.addFile(first);
			const second = ts.createSourceFile(fileName, 'function b () {}\n', ts.ScriptTarget.Latest, true);
			walker.addFile(second);

			const analysis = walker.build();
			const names = Array.from(analysis.scopes.values()).map(s => s.name);
			expect(names).to.not.include('a');
			expect(names).to.include('b');
		});
	});

	describe('this parameters (mnemonica handlers)', () => {
		it('should record `this` as immutable with its annotation as inferredType', () => {
			const code = [
				'function handler (this: UserEntity, data: { id: string }) {',
				'\tthis.id = data.id;',
				'}',
				'',
			].join('\n');
			const { analysis } = walkInline({ 'handler.ts' : code });
			const scopeId = `${virtualPath('handler.ts')}:1:1`;
			const thisVar = analysis.variables.get(`${scopeId}#this`);
			expect(thisVar).to.exist;
			expect(thisVar?.isParameter).to.be.true;
			expect(thisVar?.isMutable).to.be.false;
			expect(thisVar?.inferredType).to.equal('UserEntity');
		});
	});

	describe('fixture program (module-graph fixtures)', () => {
		const fixturesDir = path.join(__dirname, 'fixtures', 'module-graph');
		let analysis: ScopeAnalysis;

		before(() => {
			const tsconfigPath = path.join(fixturesDir, 'tsconfig.json');
			const configFile = ts.readConfigFile(tsconfigPath, ts.sys.readFile);
			const parsed = ts.parseJsonConfigFileContent(configFile.config, ts.sys, fixturesDir);
			const program = ts.createProgram({
				rootNames : parsed.fileNames,
				options   : parsed.options,
			});

			const walker = new LocalScopeWalker();
			for (const sourceFile of program.getSourceFiles()) {
				if (sourceFile.isDeclarationFile) {
					continue;
				}
				if (!path.resolve(sourceFile.fileName).startsWith(fixturesDir + path.sep)) {
					continue;
				}
				walker.addFile(sourceFile);
			}
			analysis = walker.build();
		});

		it('should create one module scope per fixture file', () => {
			const moduleScopes = Array.from(analysis.scopes.values()).filter(s => s.kind === 'module');
			// 12 fixture files (incl. builtins.ts and cjs.js)
			expect(moduleScopes).to.have.length(12);
		});

		it('should track runConsumer with its const bindings', () => {
			const scope = Array.from(analysis.scopes.values()).find(s =>
				s.name === 'runConsumer' && s.filePath.endsWith('consumer.ts'));
			expect(scope).to.exist;
			expect(scope?.kind).to.equal('function');

			const vars = Array.from(analysis.variables.values()).filter(v => v.scopeId === scope?.scopeId);
			const byName = new Map(vars.map(v => [ v.name, v ]));
			expect(byName.get('widget')?.isMutable).to.be.false;
			expect(byName.get('widget')?.inferredType).to.equal('DefaultWidget');
			expect(byName.get('thing')?.inferredType).to.equal('RenamedShape');
		});

		it('should track defs.ts makeThing as a named function scope', () => {
			const scope = Array.from(analysis.scopes.values()).find(s =>
				s.name === 'makeThing' && s.filePath.endsWith('defs.ts'));
			expect(scope).to.exist;
			expect(scope?.kind).to.equal('function');
		});

		it('should walk JS sources too (cjs.js)', () => {
			const moduleScope = analysis.scopes.get(path.join(fixturesDir, 'cjs.js'));
			expect(moduleScope).to.exist;
			const vars = Array.from(analysis.variables.values()).filter(v => v.scopeId === moduleScope?.scopeId);
			expect(vars.map(v => v.name)).to.include('defs');
		});
	});
});
