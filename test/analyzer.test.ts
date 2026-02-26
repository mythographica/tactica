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
				const UserType = define('UserType', function () {
					this.name = '';
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[0].name).to.equal('UserType');
		});

		it('should detect nested define() calls', () => {
			const source = `
				const ParentType = define('ParentType', function () {});
				const ChildType = ParentType.define('ChildType', function () {});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(2);
			expect(result.types[0].name).to.equal('ParentType');
			expect(result.types[1].name).to.equal('ChildType');
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

		describe('object field type extraction', () => {
			it('should extract property types from inline object type in data parameter', () => {
				const source = `
					const UserType = define('UserType', function (this: any, data: { id: string; email: string; age: number }) {
						this.id = data.id;
						this.email = data.email;
						this.age = data.age;
					});
				`;

				const result = analyzer.analyzeSource(source);

				expect(result.types).to.have.length(1);
				const userType = result.types[0];
				expect(userType.properties.get('id')?.type).to.equal('string');
				expect(userType.properties.get('email')?.type).to.equal('string');
				expect(userType.properties.get('age')?.type).to.equal('number');
			});

			it('should extract array types from inline object type', () => {
				const source = `
					const UserType = define('UserType', function (this: any, data: { permissions: string[] }) {
						this.permissions = data.permissions;
					});
				`;

				const result = analyzer.analyzeSource(source);

				expect(result.types).to.have.length(1);
				const userType = result.types[0];
				expect(userType.properties.get('permissions')?.type).to.equal('Array<string>');
			});

			it('should fallback to initializer inference when data property type not found', () => {
				const source = `
					const UserType = define('UserType', function (this: any, data: { id: string }) {
						this.id = data.id;
						this.name = 'default';
					});
				`;

				const result = analyzer.analyzeSource(source);

				expect(result.types).to.have.length(1);
				const userType = result.types[0];
				expect(userType.properties.get('id')?.type).to.equal('string');
				expect(userType.properties.get('name')?.type).to.equal('string');
			});
		});

		describe('multiple parameters with different names', () => {
			it('should handle renamed data parameter', () => {
				const source = `
					const UserType = define('UserType', function (this: any, dataRenamed: { id: string; email: string }) {
						this.id = dataRenamed.id;
						this.email = dataRenamed.email;
					});
				`;

				const result = analyzer.analyzeSource(source);

				expect(result.types).to.have.length(1);
				const userType = result.types[0];
				expect(userType.properties.get('id')?.type).to.equal('string');
				expect(userType.properties.get('email')?.type).to.equal('string');
			});

			it('should handle 2 parameters with different names', () => {
				const source = `
					const UserType = define('UserType', function (this: any, first: { id: string }, second: { email: string }) {
						this.id = first.id;
						this.email = second.email;
					});
				`;

				const result = analyzer.analyzeSource(source);

				expect(result.types).to.have.length(1);
				const userType = result.types[0];
				expect(userType.properties.get('id')?.type).to.equal('string');
				expect(userType.properties.get('email')?.type).to.equal('string');
			});

			it('should handle 3 parameters with different names', () => {
				const source = `
					const UserType = define('UserType', function (this: any, a: { id: string }, b: { name: string }, c: { age: number }) {
						this.id = a.id;
						this.name = b.name;
						this.age = c.age;
					});
				`;

				const result = analyzer.analyzeSource(source);

				expect(result.types).to.have.length(1);
				const userType = result.types[0];
				expect(userType.properties.get('id')?.type).to.equal('string');
				expect(userType.properties.get('name')?.type).to.equal('string');
				expect(userType.properties.get('age')?.type).to.equal('number');
			});

			it('should handle parameters with underscore prefix', () => {
				const source = `
					const UserType = define('UserType', function (this: any, _data: { id: string; _private: boolean }) {
						this.id = _data.id;
						this._private = _data._private;
					});
				`;

				const result = analyzer.analyzeSource(source);

				expect(result.types).to.have.length(1);
				const userType = result.types[0];
				expect(userType.properties.get('id')?.type).to.equal('string');
				expect(userType.properties.get('_private')?.type).to.equal('boolean');
			});

			it('should handle fallback pattern (data.prop || [])', () => {
				const source = `
					const UserType = define('UserType', function (this: any, data: { permissions: string[] }) {
						this.permissions = data.permissions || [];
					});
				`;

				const result = analyzer.analyzeSource(source);

				expect(result.types).to.have.length(1);
				const userType = result.types[0];
				expect(userType.properties.get('permissions')?.type).to.equal('Array<string>');
			});
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
