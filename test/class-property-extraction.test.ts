'use strict';

import { expect } from 'chai';
import { MnemonicaAnalyzer } from '../src/analyzer';

describe('Class Property Extraction', () => {
	let analyzer: MnemonicaAnalyzer;

	beforeEach(() => {
		analyzer = new MnemonicaAnalyzer();
	});

	describe('define() with class expression', () => {
		it('should extract class properties from define() with class', () => {
			const source = `
				import { define } from 'mnemonica';

				export const Usages = define('Usages', class {
					createdAt: number;
					private map: Map<string, object[]>;
					constructor() {
						this.createdAt = Date.now();
						this.map = new Map();
					}
					has (name: string) {
						return this.map.has(name);
					}
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			
			const [ usageType ] = result.types;
			expect(usageType.name).to.equal('Usages');
			// Now includes both createdAt property and has method
			expect(usageType.properties.size).to.equal(2);
			
			// Check createdAt property (public)
			expect(usageType.properties.has('createdAt')).to.be.true;
			expect(usageType.properties.get('createdAt')?.type).to.equal('number');
			
			// Check has method is extracted
			expect(usageType.properties.has('has')).to.be.true;
			
			// Check map property is NOT present (it's private)
			expect(usageType.properties.has('map')).to.be.false;
		});

		it('should extract class with property initializers', () => {
			const source = `
				import { define } from 'mnemonica';

				export const User = define('User', class {
					name: string = '';
					age: number = 0;
					active: boolean = true;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			
			const [ userType ] = result.types;
			expect(userType.name).to.equal('User');
			expect(userType.properties.size).to.equal(3);
			
			expect(userType.properties.get('name')?.type).to.equal('string');
			expect(userType.properties.get('age')?.type).to.equal('number');
			expect(userType.properties.get('active')?.type).to.equal('boolean');
		});

		it('should extract class with optional properties', () => {
			const source = `
				import { define } from 'mnemonica';

				export const Profile = define('Profile', class {
					id: string;
					bio?: string;
					avatar?: string;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			
			const [ profileType ] = result.types;
			expect(profileType.properties.get('id')?.optional).to.be.false;
			expect(profileType.properties.get('bio')?.optional).to.be.true;
			expect(profileType.properties.get('avatar')?.optional).to.be.true;
		});

		it('should extract class with array types', () => {
			const source = `
				import { define } from 'mnemonica';

				export const Container = define('Container', class {
					items: string[];
					counts: Array<number>;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			
			const [ containerType ] = result.types;
			expect(containerType.properties.get('items')?.type).to.equal('Array<string>');
			expect(containerType.properties.get('counts')?.type).to.equal('Array<number>');
		});

		it('should handle empty class', () => {
			const source = `
				import { define } from 'mnemonica';

				export const Empty = define('Empty', class {
					constructor() {}
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[ 0 ].properties.size).to.equal(0);
		});

		it('should extract constructor params with typed parameters from class expression', () => {
			const source = `
				import { define } from 'mnemonica';

				export const UserType = define('UserType', class {
					name: string = '';
					count: number = 0;
					constructor(name: string, count: number) {
						this.name = name;
						this.count = count;
					}
				});
			`;

			const graph = analyzer.analyzeSource(source);
			expect(graph.errors).to.have.length(0);
			const [ userType ] = graph.types;
			expect(userType.name).to.equal('UserType');
			const params = userType.constructorParams;
			expect(params).to.be.an('array');
			expect(params!.find(p => p.name === 'name')?.type).to.equal('string');
			expect(params!.find(p => p.name === 'count')?.type).to.equal('number');
		});
	});

	describe('method return annotations with non-graph outer generics (0.2.0 emission restoration)', () => {
		const generateContent = (): string => {
			const { TypesGenerator } = require('../src/generator') as typeof import('../src/generator');
			const generator = new TypesGenerator(analyzer.getGraph());
			const { content } = generator.generateTypesFile();
			return content;
		};

		it('keeps ambient outer generics verbatim with inner graph aliases resolved', () => {
			analyzer.analyzeSource(`
import { define } from 'mnemonica';

const EDSRoot = define('EDSRoot', function (this: EDSRoot) {
	this.kind = 'root';
});
EDSRoot.define('SomeEntry', function (this: SomeEntry, data: { tag: string }) {
	this.tag = data.tag;
});

@decorate(EDSRoot)
class LogIndex {
	entries (): MapIterator<[string, SomeEntry[]]> {
		return undefined;
	}
}
`, 'log-index.ts');

			const content = generateContent();
			expect(content).to.include('entries: () => MapIterator<[string, Array<EDSRoot_SomeEntry>]>');
		});

		it('resolves a bare graph-type return to the generated alias', () => {
			analyzer.analyzeSource(`
import { define } from 'mnemonica';

const EDSRoot = define('EDSRoot', function (this: EDSRoot) {
	this.kind = 'root';
});
EDSRoot.define('SomeEntry', function (this: SomeEntry, data: { tag: string }) {
	this.tag = data.tag;
});

@decorate(EDSRoot)
class LogIndex {
	first (): SomeEntry {
		return undefined;
	}
}
`, 'log-index.ts');

			const content = generateContent();
			expect(content).to.include('first: () => EDSRoot_SomeEntry');
		});

		it('drops the InstanceType wrapper through local aliases — InstanceType<typeof X> → generated alias (0.2.0 law)', () => {
			analyzer.analyzeSource(`
import { define } from 'mnemonica';

const EntryRoot = define('EntryRoot', function (this: EntryRoot) {
	this.kind = 'root';
});
EntryRoot.define('LogEntry', function (this: LogEntry, data: { tag: string }) {
	this.tag = data.tag;
});

export type LogEntryInstance = InstanceType<typeof LogEntry>;

@decorate(EntryRoot)
class LogIndex {
	get (name: string): LogEntryInstance | undefined {
		return undefined;
	}
	all (): Array<LogEntryInstance> {
		return undefined;
	}
}
`, 'log-index.ts');

			const content = generateContent();
			// wrapper dropped — the generated alias already IS the instance type
			expect(content).to.include('get: (name: string) => EntryRoot_LogEntry | undefined;');
			expect(content).to.include('all: () => Array<EntryRoot_LogEntry>;');
			expect(content).to.not.include('InstanceType');
		});

		it('degrades the WHOLE InstanceType expression when the query does not resolve — never emits InstanceType<unknown> (invalid TS)', () => {
			analyzer.analyzeSource(`
import { define } from 'mnemonica';

const EntryRoot = define('EntryRoot', function (this: EntryRoot) {
	this.kind = 'root';
});

export type GhostInstance = InstanceType<typeof NotAGraphType>;

@decorate(EntryRoot)
class LogIndex {
	ghost (): GhostInstance {
		return undefined;
	}
}
`, 'log-index.ts');

			const content = generateContent();
			expect(content).to.include('ghost: () => unknown;');
			expect(content).to.not.include('InstanceType<unknown>');
			expect(content).to.not.include('InstanceType');
		});

		it('never emits a project-local non-graph name verbatim — ambiguous declarations degrade to unknown (fatal per the ambiguity law)', () => {
			analyzer.analyzeSource(`
export interface LocalBox<T> {
	a: T;
}
`, 'box-a.ts');
			analyzer.analyzeSource(`
export interface LocalBox<T> {
	b: T;
}
`, 'box-b.ts');
			analyzer.analyzeSource(`
import { define } from 'mnemonica';

const EDSRoot = define('EDSRoot', function (this: EDSRoot) {
	this.kind = 'root';
});
EDSRoot.define('SomeEntry', function (this: SomeEntry, data: { tag: string }) {
	this.tag = data.tag;
});

@decorate(EDSRoot)
class LogIndex {
	boxed (): LocalBox<SomeEntry> {
		return undefined;
	}
}
`, 'log-index.ts');

			const content = generateContent();
			expect(content).to.include('boxed: () => unknown');
			expect(content).to.not.include('LocalBox');
			// the ambiguity itself is the hard-fail class — surfaced, not hidden
			expect(analyzer.getResolutionErrors().length).to.be.greaterThan(0);
		});
	});

	describe('UsageEntry pattern from Usages.ts', () => {
		it('should extract properties from UsageEntry using Object.defineProperties pattern', () => {
			const source = `
				import { define } from 'mnemonica';

				export type usage = {
					id: string;
					typeName: string;
					filePath: string;
					line: number;
					column: number;
					context: string
				};

				export const Usages = define('Usages', class {
					createdAt: number;
					private map: Map<string, object[]>;
					constructor() {
						this.createdAt = Date.now();
						this.map = new Map();
					}
				});

				const setProps = (to: object, from: object) => {
					Object.defineProperties(to, Object.getOwnPropertyDescriptors(from));
				}

				export const UsageEntry = Usages.define('UsageEntry', function (
					this: usage,
					data: usage
				) {
					setProps(this, data);
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(2);
			
			// Find UsageEntry type
			const usageEntryType = result.types.find(t => t.name === 'UsageEntry');
			expect(usageEntryType).to.exist;
			
			// UsageEntry should have properties from the 'usage' type
			// This is the key test - it should NOT be empty
			console.log('UsageEntry properties:', Array.from(usageEntryType!.properties.entries()));
			expect(usageEntryType!.properties.size).to.be.at.least(1, 'UsageEntry should have at least 1 property');
			
			// Check that it has the expected properties
			expect(usageEntryType!.properties.has('id')).to.be.true;
			expect(usageEntryType!.properties.has('typeName')).to.be.true;
			expect(usageEntryType!.properties.has('filePath')).to.be.true;
		});
	});
});
