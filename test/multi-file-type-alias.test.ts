'use strict';

import { expect } from 'chai';
import { MnemonicaAnalyzer } from '../src/analyzer';

describe('Multi-file type alias resolution', () => {
	it('should resolve type alias when analyzing files separately', () => {
		const analyzer = new MnemonicaAnalyzer();

		// First file defines the type alias
		const file1Source = `
			export type usage = {
				id: string;
				typeName: string;
				filePath: string;
				line: number;
				column: number;
				context: string
			};
		`;

		const result1 = analyzer.analyzeSource(file1Source, 'types.ts');
		expect(result1.errors).to.have.length(0);

		// Second file uses the type alias in `this` parameter
		const file2Source = `
			import { define } from 'mnemonica';
			import { usage } from './types';

			export const Usages = define('Usages', class {
				createdAt: number;
				constructor() {
					this.createdAt = Date.now();
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

		const result2 = analyzer.analyzeSource(file2Source, 'Usages.ts');
		expect(result2.errors).to.have.length(0);

		// Find UsageEntry type
		const usageEntryType = result2.types.find(t => t.name === 'UsageEntry');
		expect(usageEntryType).to.exist;

		// UsageEntry should have properties from the 'usage' type
		console.log('UsageEntry properties (separate files):', Array.from(usageEntryType!.properties.entries()));
		expect(usageEntryType!.properties.size).to.be.at.least(1, 'UsageEntry should have at least 1 property');
	});

	it('should resolve type alias when both are in the same file', () => {
		const analyzer = new MnemonicaAnalyzer();

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
				constructor() {
					this.createdAt = Date.now();
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

		// Find UsageEntry type
		const usageEntryType = result.types.find(t => t.name === 'UsageEntry');
		expect(usageEntryType).to.exist;

		// UsageEntry should have properties from the 'usage' type
		console.log('UsageEntry properties (same file):', Array.from(usageEntryType!.properties.entries()));
		expect(usageEntryType!.properties.size).to.be.at.least(1, 'UsageEntry should have at least 1 property');
	});
});
