'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as path from 'path';
import { TypesWriter } from '../src/writer';
import { GeneratedTypes } from '../src/types';

describe('TypesWriter', () => {
	const testDir = path.join(__dirname, '.test-mnemonica');
	let writer: TypesWriter;

	describe('default constructor', () => {
		it('should use .tactica as default output directory', () => {
			const defaultWriter = new TypesWriter();
			expect(defaultWriter.getOutputDir()).to.equal('.tactica');
		});
	});

	beforeEach(() => {
		// Clean up test directory
		if (fs.existsSync(testDir)) {
			fs.rmSync(testDir, { recursive : true });
		}
		writer = new TypesWriter(testDir);
	});

	afterEach(() => {
		if (fs.existsSync(testDir)) {
			fs.rmSync(testDir, { recursive : true });
		}
	});

	describe('write()', () => {
		it('should create output directory', () => {
			const generated: GeneratedTypes = {
				content : '// test',
				types   : [ 'TestType' ],
			};

			writer.write(generated);

			expect(fs.existsSync(testDir)).to.be.true;
		});

		it('should write types.ts file', () => {
			const generated: GeneratedTypes = {
				content : '// test content',
				types   : [ 'TestType' ],
			};

			const outputPath = writer.write(generated);

			expect(fs.existsSync(outputPath)).to.be.true;
			const content = fs.readFileSync(outputPath, 'utf-8');
			expect(content).to.equal('// test content');
		});

		it('should return correct path', () => {
			const generated: GeneratedTypes = {
				content : '// test',
				types   : [],
			};

			const outputPath = writer.write(generated);

			expect(outputPath).to.equal(path.join(testDir, 'types.ts'));
		});
	});

	describe('clean()', () => {
		it('should remove all files in output directory', () => {
			const generated: GeneratedTypes = {
				content : '// test',
				types   : [],
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

	describe('writeTo()', () => {
		it('should write to custom filename', () => {
			const generated: GeneratedTypes = {
				content : '// custom content',
				types   : [ 'CustomType' ],
			};

			const outputPath = writer.writeTo('custom.ts', generated.content);

			expect(fs.existsSync(outputPath)).to.be.true;
			expect(path.basename(outputPath)).to.equal('custom.ts');
			const content = fs.readFileSync(outputPath, 'utf-8');
			expect(content).to.equal('// custom content');
		});

		it('should create output directory if not exists', () => {
			const nestedDir = path.join(__dirname, '.nested-test');
			const nestedWriter = new TypesWriter(nestedDir);

			nestedWriter.writeTo('file.ts', '// test');

			expect(fs.existsSync(nestedDir)).to.be.true;

			// Cleanup
			fs.rmSync(nestedDir, { recursive : true, force : true });
		});
	});

	describe('writeDefinitionsFile()', () => {
		it('should write definitions.json with correct shape', () => {
			const definitions = new Map([
				[ 'UserType', {
					name        : 'UserType',
					location    : 'src/users.ts:10:7',
					kind        : 'define' as const,
					parent      : null,
					strictChain : true,
					blockErrors : false,
				} ],
			]);

			const outputPath = writer.writeDefinitionsFile(definitions);

			expect(fs.existsSync(outputPath)).to.be.true;
			expect(path.basename(outputPath)).to.equal('definitions.json');
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.version).to.equal('1.0');
			expect(json.definitions.UserType.name).to.equal('UserType');
			expect(json.definitions.UserType.kind).to.equal('define');
		});

		it('should handle empty definitions map', () => {
			const outputPath = writer.writeDefinitionsFile(new Map());
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.definitions).to.deep.equal({});
		});
	});

	describe('writeUsagesFile()', () => {
		it('should write usages.json with correct shape', () => {
			const usages = new Map([
				[ 'UserType', [
					{ location : 'src/main.ts:3:7', kind : 'instantiation' as const, code : 'new UserType({})' },
				] ],
			]);

			const outputPath = writer.writeUsagesFile(usages);

			expect(fs.existsSync(outputPath)).to.be.true;
			expect(path.basename(outputPath)).to.equal('usages.json');
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.version).to.equal('1.0');
			expect(json.usages.UserType).to.have.length(1);
			expect(json.usages.UserType[ 0 ].kind).to.equal('instantiation');
		});

		it('should handle empty usages map', () => {
			const outputPath = writer.writeUsagesFile(new Map());
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.usages).to.deep.equal({});
		});
	});

	describe('writeEDSFile()', () => {
		it('should write eds.json with correct shape', () => {
			const eds = new Map([
				[ 'UserEntity', [
					{ location : 'src/queue.ts:45:12', kind : 'wrap' as const, code : 'wrap(process)', targetType : 'UserEntity' },
				] ],
			]);

			const outputPath = writer.writeEDSFile(eds);

			expect(fs.existsSync(outputPath)).to.be.true;
			expect(path.basename(outputPath)).to.equal('eds.json');
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.version).to.equal('1.0');
			expect(json.eds.UserEntity).to.have.length(1);
			expect(json.eds.UserEntity[ 0 ].kind).to.equal('wrap');
		});

		it('should handle empty eds map', () => {
			const outputPath = writer.writeEDSFile(new Map());
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.eds).to.deep.equal({});
		});
	});

	describe('writeFlowFile()', () => {
		it('should write flow.json with correct shape', () => {
			const flow = new Map([
				[ 'UserType', [
					{ location : 'src/main.ts:7:5', kind : 'propertyRead' as const, code : 'user.name' },
				] ],
			]);

			const outputPath = writer.writeFlowFile(flow);

			expect(fs.existsSync(outputPath)).to.be.true;
			expect(path.basename(outputPath)).to.equal('flow.json');
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.version).to.equal('1.0');
			expect(json.flow.UserType).to.have.length(1);
			expect(json.flow.UserType[ 0 ].kind).to.equal('propertyRead');
		});

		it('should handle empty flow map', () => {
			const outputPath = writer.writeFlowFile(new Map());
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.flow).to.deep.equal({});
		});
	});

	describe('writeHierarchyFile()', () => {
		it('should write hierarchy.json with correct shape', () => {
			const roots = [
				{
					name     : 'UserType',
					fullPath : 'UserType',
					location : 'src/users.ts:10:7',
					children : [
						{
							name     : 'AdminType',
							fullPath : 'UserType.AdminType',
							location : 'src/users.ts:20:7',
							children : [],
						},
					],
				},
			];

			const outputPath = writer.writeHierarchyFile(roots);

			expect(fs.existsSync(outputPath)).to.be.true;
			expect(path.basename(outputPath)).to.equal('hierarchy.json');
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.version).to.equal('1.0');
			expect(json.roots).to.have.length(1);
			expect(json.roots[ 0 ].fullPath).to.equal('UserType');
			expect(json.roots[ 0 ].children[ 0 ].fullPath).to.equal('UserType.AdminType');
		});

		it('should handle empty roots array', () => {
			const outputPath = writer.writeHierarchyFile([]);
			const json = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
			expect(json.roots).to.deep.equal([]);
		});
	});
});
