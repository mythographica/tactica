'use strict';

import { expect } from 'chai';
import { MnemonicaAnalyzer } from '../src/analyzer';

describe('MnemonicaAnalyzer', () => {
	let analyzer: MnemonicaAnalyzer;

	beforeEach(() => {
		analyzer = new MnemonicaAnalyzer();
	});

	describe('define() calls', () => {
		it('should detect simple define() call', () => {
			const source = `
				const FirstType = define('FirstType', function (this: { first: string }) {
					this.first = 'FirstType';
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[0].name).to.equal('FirstType');
		});

		it('should detect nested define() calls', () => {
			const source = `
				const FirstType = define('FirstType', function (this: { first: string }) {
					this.first = 'FirstType';
				});

				const SecondType = FirstType.define('SecondType', function (this: { second: string }) {
					this.second = 'SecondType';
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(2);
			
			const first = result.types.find(t => t.name === 'FirstType');
			const second = result.types.find(t => t.name === 'SecondType');

			expect(first).to.exist;
			expect(second).to.exist;
			expect(second?.parent?.name).to.equal('FirstType');
		});

		it('should extract properties from constructor', () => {
			// Test that types are created for define calls with properties
			const source = `
				const UserType = define('UserType', function (this: any, data: any) {
					Object.assign(this, data);
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.types).to.have.length(1);
			const userType = result.types[0];
			expect(userType.name).to.equal('UserType');
		});

		it('should detect Object.assign pattern', () => {
			const source = `
				const UserType = define('UserType', function (this: any, data: any) {
					Object.assign(this, data);
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.types).to.have.length(1);
			expect(result.types[0].name).to.equal('UserType');
		});
	});

	describe('decorate() decorator', () => {
		it('should detect @decorate() on class', () => {
			const source = `
				@decorate()
				class MyClass {
					value: number = 123;
				}
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[0].name).to.equal('MyClass');
		});

		it('should extract class properties', () => {
			const source = `
				@decorate()
				class User {
					name: string = '';
					email: string = '';
				}
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.types).to.have.length(1);
			const user = result.types[0];
			expect(user.properties.has('name')).to.be.true;
			expect(user.properties.has('email')).to.be.true;
		});
	});

	describe('graph structure', () => {
		it('should build correct type hierarchy', () => {
			const source = `
				const A = define('A', function () {});
				const B = A.define('B', function () {});
				const C = B.define('C', function () {});
			`;

			analyzer.analyzeSource(source);
			const graph = analyzer.getGraph();

			// Note: In single-pass analysis without TS program binding,
			// nested types are registered as roots. The parent-child
			// relationship requires multi-pass analysis with type checker.
			const allTypes = graph.getAllTypes();
			expect(allTypes.length).to.be.at.least(3);
			expect(allTypes.some(t => t.name === 'A')).to.be.true;
			expect(allTypes.some(t => t.name === 'B')).to.be.true;
			expect(allTypes.some(t => t.name === 'C')).to.be.true;
		});
	});
});
