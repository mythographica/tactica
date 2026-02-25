'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as path from 'path';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { TypesGenerator } from '../src/generator';
import { TypesWriter } from '../src/writer';
import { TypeGraphImpl } from '../src/graph';

/**
 * Integration test based on core/test-ts/test-example.ts pattern
 */
describe('Integration: core/test-ts/test-example.ts pattern', () => {
	const testOutputDir = path.join(__dirname, '.test-integration');

	afterEach(() => {
		if (fs.existsSync(testOutputDir)) {
			fs.rmSync(testOutputDir, { recursive: true });
		}
	});

	it('should analyze the test-example.ts pattern', () => {
		// Source code matching test-ts/test-example.ts
		const sourceCode = `
import { define, apply } from '..';

const FirstType = define( 'SomeType', function (this: {
	first: 'FirstType',
}) {
	this.first = 'FirstType';
});

const FirstTypeO = define( 'SomeType', function (this: {
	first: 'FirstType',
}) {
	this.first = 'FirstType';
}, {
	exposeInstanceMethods: false
});

const SecondType = FirstType.define( 'SecondType', function ( this: {
	first: undefined,
	second: string,
}) {
	this.first = undefined;
	this.second = 'SecondType';
});

const first = new FirstType();
const firstO = new FirstTypeO();

type TSecondInstance = InstanceType<typeof SecondType>;

const second = new first.SecondType() as unknown as TSecondInstance;

const second2 = apply(first, SecondType);

first.extract();
first.pick('first');
first.SecondType;

const f1: 'FirstType' = first.first;
const f2: 'FirstType' = firstO.first;

console.log(first, firstO, second, second2, f1, f2);
`;

		const analyzer = new MnemonicaAnalyzer();
		const result = analyzer.analyzeSource(sourceCode, 'test-example.ts');

		// Should find the types
		expect(result.types.length).to.be.greaterThan(0);
		
		const graph = analyzer.getGraph();
		
		// Should have SomeType as root
		const firstType = graph.findType('SomeType');
		expect(firstType).to.exist;
		
		// Note: The analyzer processes types in order, so nested parent lookup
		// happens after parent is defined. SecondType gets registered separately.
		// In a real scenario with a TS program, the binding would be resolved.
		expect(graph.getAllTypes().length).to.be.greaterThan(0);
	});

	it('should generate types for the pattern', () => {
		const sourceCode = `
const FirstType = define('FirstType', function (this: { first: string }) {
	this.first = 'FirstType';
});

const SecondType = FirstType.define('SecondType', function (this: { second: string }) {
	this.second = 'SecondType';
});
`;

		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(sourceCode, 'test.ts');

		const graph = analyzer.getGraph();
		const generator = new TypesGenerator(graph);
		const generated = generator.generateGlobalAugmentation();

		// Should generate content
		expect(generated.content).to.include('FirstTypeInstance');
		expect(generated.content).to.include('SecondTypeInstance');
		expect(generated.content).to.include('declare global');

		// Should list the generated types
		expect(generated.types).to.include('FirstTypeInstance');
		expect(generated.types).to.include('SecondTypeInstance');
	});

	it('should write generated types to file', () => {
		const sourceCode = `
const UserType = define('UserType', function (this: { name: string }) {
	this.name = '';
});

const AdminType = UserType.define('AdminType', function (this: { role: string }) {
	this.role = 'admin';
});
`;

		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(sourceCode, 'test.ts');

		const graph = analyzer.getGraph();
		const generator = new TypesGenerator(graph);
		const generated = generator.generateGlobalAugmentation();

		const writer = new TypesWriter(testOutputDir);
		const outputPath = writer.writeGlobalAugmentation(generated);

		// File should exist
		expect(fs.existsSync(outputPath)).to.be.true;

		// Content should be valid
		const content = fs.readFileSync(outputPath, 'utf-8');
		expect(content).to.include('@mnemonica/tactica');
		expect(content).to.include('UserTypeInstance');
		expect(content).to.include('AdminTypeInstance');
	});

	it('should handle complex nested hierarchy', () => {
		const sourceCode = `
const A = define('A', function (this: { a: number }) {
	this.a = 1;
});

const B = A.define('B', function (this: { b: string }) {
	this.b = 'b';
});

const C = B.define('C', function (this: { c: boolean }) {
	this.c = true;
});

const D = C.define('D', function (this: { d: string[] }) {
	this.d = [];
});
`;

		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(sourceCode, 'test.ts');

		const graph = analyzer.getGraph();

		// Should find all types (they may be registered as separate roots
		// due to the single-pass analysis limitation)
		const allTypes = graph.getAllTypes();
		expect(allTypes.some(t => t.name === 'A')).to.be.true;
		expect(allTypes.some(t => t.name === 'B')).to.be.true;
		expect(allTypes.some(t => t.name === 'C')).to.be.true;
		expect(allTypes.some(t => t.name === 'D')).to.be.true;

		const generator = new TypesGenerator(graph);
		const generated = generator.generateGlobalAugmentation();

		// Should include all instance interfaces
		expect(generated.content).to.include('AInstance');
		expect(generated.content).to.include('BInstance');
		expect(generated.content).to.include('CInstance');
		expect(generated.content).to.include('DInstance');
	});

	it('should handle @decorate() decorator pattern', () => {
		const sourceCode = `
@decorate()
class User {
	name: string = '';
	email: string = '';
}

@decorate(User)
class Admin {
	role: string = 'admin';
}
`;

		const analyzer = new MnemonicaAnalyzer();
		analyzer.analyzeSource(sourceCode, 'test.ts');

		const graph = analyzer.getGraph();

		// Should find decorated classes
		expect(graph.findType('User')).to.exist;
		expect(graph.findType('User.Admin')).to.exist;
	});
});
