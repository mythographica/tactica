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
			
			const usageType = result.types[0];
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
			
			const userType = result.types[0];
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
			
			const profileType = result.types[0];
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
			
			const containerType = result.types[0];
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
			expect(result.types[0].properties.size).to.equal(0);
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
