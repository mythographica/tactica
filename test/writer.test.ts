'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as path from 'path';
import { TypesWriter } from '../src/writer';
import { GeneratedTypes } from '../src/types';

describe('TypesWriter', () => {
	const testDir = path.join(__dirname, '.test-mnemonica');
	let writer: TypesWriter;

	beforeEach(() => {
		// Clean up test directory
		if (fs.existsSync(testDir)) {
			fs.rmSync(testDir, { recursive: true });
		}
		writer = new TypesWriter(testDir);
	});

	afterEach(() => {
		if (fs.existsSync(testDir)) {
			fs.rmSync(testDir, { recursive: true });
		}
	});

	describe('write()', () => {
		it('should create output directory', () => {
			const generated: GeneratedTypes = {
				content: '// test',
				types: ['TestType'],
			};

			writer.write(generated);

			expect(fs.existsSync(testDir)).to.be.true;
		});

		it('should write types.d.ts file', () => {
			const generated: GeneratedTypes = {
				content: '// test content',
				types: ['TestType'],
			};

			const outputPath = writer.write(generated);

			expect(fs.existsSync(outputPath)).to.be.true;
			const content = fs.readFileSync(outputPath, 'utf-8');
			expect(content).to.equal('// test content');
		});

		it('should return correct path', () => {
			const generated: GeneratedTypes = {
				content: '// test',
				types: [],
			};

			const outputPath = writer.write(generated);

			expect(outputPath).to.equal(path.join(testDir, 'types.d.ts'));
		});
	});

	describe('clean()', () => {
		it('should remove all files in output directory', () => {
			const generated: GeneratedTypes = {
				content: '// test',
				types: [],
			};

			writer.write(generated);
			writer.clean();

			const files = fs.existsSync(testDir)
				? fs.readdirSync(testDir)
				: [];
			expect(files).to.have.length(0);
		});
	});

	describe('getOutputDir()', () => {
		it('should return the output directory', () => {
			expect(writer.getOutputDir()).to.equal(testDir);
		});
	});
});
