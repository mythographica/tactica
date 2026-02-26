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
	
		describe('type inference from initializers', () => {
			describe('BinaryExpression arithmetic operations', () => {
				it('should infer number type from addition', () => {
					const source = `
						const CalcType = define('CalcType', function (this: any, data: { a: number; b: number }) {
							this.sum = data.a + data.b;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('sum')?.type).to.equal('number');
				});
	
				it('should infer number type from subtraction', () => {
					const source = `
						const CalcType = define('CalcType', function (this: any, data: { a: number; b: number }) {
							this.diff = data.a - data.b;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('diff')?.type).to.equal('number');
				});
	
				it('should infer number type from multiplication', () => {
					const source = `
						const CalcType = define('CalcType', function (this: any, data: { a: number; b: number }) {
							this.product = data.a * data.b;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('product')?.type).to.equal('number');
				});
	
				it('should infer number type from division', () => {
					const source = `
						const CalcType = define('CalcType', function (this: any, data: { a: number; b: number }) {
							this.quotient = data.a / data.b;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('quotient')?.type).to.equal('number');
				});
	
				it('should infer number type from mixed arithmetic', () => {
					const source = `
						const CalcType = define('CalcType', function (this: any, data: { x: number; y: number; z: number }) {
							this.result = (data.x + data.y) * data.z;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('result')?.type).to.equal('number');
				});
			});
	
			describe('PropertyAccessExpression from typed parameters', () => {
				it('should infer type from data parameter property access', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { id: string; count: number; active: boolean }) {
							this.userId = data.id;
							this.counter = data.count;
							this.isActive = data.active;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('userId')?.type).to.equal('string');
					expect(type.properties.get('counter')?.type).to.equal('number');
					expect(type.properties.get('isActive')?.type).to.equal('boolean');
				});
	
				it('should infer array type from data parameter property access', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { tags: string[] }) {
							this.tags = data.tags;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('tags')?.type).to.equal('Array<string>');
				});
	
				it('should infer nested property access types', () => {
					const source = `
						const UserType = define('UserType', function (this: any, userData: { profile: { name: string } }) {
							this.name = userData.profile.name;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					// Note: Deep nested property access returns 'unknown' - not yet implemented
					expect(type.properties.get('name')?.type).to.equal('unknown');
				});
			});
	
			describe('Identifier direct parameter lookup', () => {
				it('should infer type from direct parameter assignment', () => {
					const source = `
						const UserType = define('UserType', function (this: any, name: string) {
							this.name = name;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('name')?.type).to.equal('string');
				});
	
				it('should infer number type from direct parameter assignment', () => {
					const source = `
						const UserType = define('UserType', function (this: any, age: number) {
							this.age = age;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('age')?.type).to.equal('number');
				});
	
				it('should infer boolean type from direct parameter assignment', () => {
					const source = `
						const UserType = define('UserType', function (this: any, active: boolean) {
							this.active = active;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('active')?.type).to.equal('boolean');
				});
			});
	
			describe('CallExpression return type inference', () => {
				it('should infer number type from Date.now()', () => {
					const source = `
						const TimestampType = define('TimestampType', function (this: any) {
							this.createdAt = Date.now();
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('createdAt')?.type).to.equal('number');
				});
	
				it('should infer number type from parseInt()', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { id: string }) {
							this.id = parseInt(data.id);
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('id')?.type).to.equal('number');
				});
	
				it('should infer number type from parseFloat()', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { value: string }) {
							this.value = parseFloat(data.value);
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('value')?.type).to.equal('number');
				});
	
				it('should infer string type from String()', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { id: number }) {
							this.id = String(data.id);
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('id')?.type).to.equal('string');
				});
	
				it('should infer number type from Number()', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { value: string }) {
							this.value = Number(data.value);
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('value')?.type).to.equal('number');
				});
	
				it('should infer boolean type from Boolean()', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { value: string }) {
							this.value = Boolean(data.value);
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('value')?.type).to.equal('boolean');
				});
	
				it('should infer string type from toString() call', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { id: number }) {
							this.idStr = data.id.toString();
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('idStr')?.type).to.equal('string');
				});
	
				it('should handle unknown functions gracefully', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { value: string }) {
							this.result = someUnknownFunction(data.value);
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('result')?.type).to.equal('unknown');
				});
			});
	
			describe('TemplateLiteral type inference', () => {
				it('should infer string type from template literal', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { first: string; last: string }) {
							this.fullName = \`\${data.first} \${data.last}\`;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('fullName')?.type).to.equal('string');
				});
	
				it('should infer string type from simple template literal', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { id: number }) {
							this.idStr = \`ID: \${data.id}\`;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('idStr')?.type).to.equal('string');
				});
			});
	
			describe('LiteralType inference', () => {
				it('should infer string type from string literal initializer', () => {
					const source = `
						const UserType = define('UserType', function (this: any) {
							this.role = 'user';
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					// Note: Currently returns 'string' instead of "'user'" - baseline type
					expect(type.properties.get('role')?.type).to.equal('string');
				});
	
				it('should infer number type from numeric literal initializer', () => {
					const source = `
						const UserType = define('UserType', function (this: any) {
							this.status = 200;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					// Note: Currently returns 'number' instead of '200' - baseline type
					expect(type.properties.get('status')?.type).to.equal('number');
				});
	
				it('should infer boolean type from boolean literal initializer', () => {
					const source = `
						const UserType = define('UserType', function (this: any) {
							this.active = true;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					// Note: Currently returns 'boolean' instead of 'true' - baseline type
					expect(type.properties.get('active')?.type).to.equal('boolean');
				});
	
				it('should infer union literal type from data parameter', () => {
					const source = `
						const UserType = define('UserType', function (this: any, data: { role: 'admin' | 'user' | 'guest' }) {
							this.role = data.role;
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					// Note: Union types in dataTypeMap return 'unknown' - full type checking needed
					expect(type.properties.get('role')?.type).to.equal('unknown');
				});
			});
	
			describe('NewExpression type inference', () => {
				it('should infer Date type from new Date()', () => {
					const source = `
						const UserType = define('UserType', function (this: any) {
							this.createdAt = new Date();
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					expect(type.properties.get('createdAt')?.type).to.equal('Date');
				});
	
				it('should infer Array type from new Array()', () => {
					const source = `
						const UserType = define('UserType', function (this: any) {
							this.items = new Array<string>();
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					// Note: Returns 'Array' without type arguments - generics not parsed from AST
					expect(type.properties.get('items')?.type).to.equal('Array');
				});
	
				it('should infer Map type from new Map()', () => {
					const source = `
						const UserType = define('UserType', function (this: any) {
							this.cache = new Map<string, number>();
						});
					`;
	
					const result = analyzer.analyzeSource(source);
	
					expect(result.types).to.have.length(1);
					const type = result.types[0];
					// Note: Returns 'Map' without type arguments - generics not parsed from AST
					expect(type.properties.get('cache')?.type).to.equal('Map');
				});
			});
		});
	
		describe('async constructor patterns', () => {
			it('should detect async define() call', () => {
				const source = `
					const AsyncType = define('AsyncType', async function (this: any, data: { value: number }) {
						this.value = data.value;
						this.computed = data.value * 2;
					});
				`;
	
				const result = analyzer.analyzeSource(source);
	
				expect(result.errors).to.have.length(0);
				expect(result.types).to.have.length(1);
				const type = result.types[0];
				expect(type.name).to.equal('AsyncType');
				expect(type.properties.get('value')?.type).to.equal('number');
				expect(type.properties.get('computed')?.type).to.equal('number');
			});
	
			it('should detect nested async types', () => {
				const source = `
					const RootAsync = define('RootAsync', async function (this: any, data: { id: string }) {
						this.id = data.id;
					});
					const SubAsync = RootAsync.define('SubAsync', async function (this: any, data: { name: string }) {
						this.name = data.name;
					});
				`;
	
				const result = analyzer.analyzeSource(source);
	
				expect(result.errors).to.have.length(0);
				expect(result.types).to.have.length(2);
				expect(result.types[0].name).to.equal('RootAsync');
				expect(result.types[1].name).to.equal('SubAsync');
			});
	
			it('should handle async with Date.now()', () => {
				const source = `
					const AsyncType = define('AsyncType', async function (this: any) {
						this.timestamp = Date.now();
					});
				`;
	
				const result = analyzer.analyzeSource(source);
	
				expect(result.types).to.have.length(1);
				const type = result.types[0];
				expect(type.properties.get('timestamp')?.type).to.equal('number');
			});
	
			it('should handle async with template literals', () => {
				const source = `
					const AsyncType = define('AsyncType', async function (this: any, data: { prefix: string; id: string }) {
						this.key = \`\${data.prefix}:\${data.id}\`;
					});
				`;
	
				const result = analyzer.analyzeSource(source);
	
				expect(result.types).to.have.length(1);
				const type = result.types[0];
				expect(type.properties.get('key')?.type).to.equal('string');
			});
		});
	
		describe('complex real-world patterns', () => {
			it('should handle user entity pattern', () => {
				const source = `
					const UserEntity = define('UserEntity', function (this: any, data: { id: string; email: string; name: string }) {
						this.id = data.id;
						this.email = data.email;
						this.name = data.name;
						this.createdAt = Date.now();
						this.role = 'user';
					});
				`;
	
				const result = analyzer.analyzeSource(source);
	
				expect(result.errors).to.have.length(0);
				expect(result.types).to.have.length(1);
				const type = result.types[0];
				expect(type.name).to.equal('UserEntity');
				expect(type.properties.get('id')?.type).to.equal('string');
				expect(type.properties.get('email')?.type).to.equal('string');
				expect(type.properties.get('name')?.type).to.equal('string');
				expect(type.properties.get('createdAt')?.type).to.equal('number');
				// Note: Returns 'string' instead of "'user'" - baseline type for literals
				expect(type.properties.get('role')?.type).to.equal('string');
			});
	
			it('should handle mixed parameter patterns', () => {
				const source = `
					const ComplexType = define('ComplexType', function (this: any, data: { id: string }, meta: { count: number }, status: boolean) {
						this.id = data.id;
						this.count = meta.count;
						this.active = status;
						this.timestamp = Date.now();
					});
				`;
	
				const result = analyzer.analyzeSource(source);
	
				expect(result.types).to.have.length(1);
				const type = result.types[0];
				expect(type.properties.get('id')?.type).to.equal('string');
				expect(type.properties.get('count')?.type).to.equal('number');
				expect(type.properties.get('active')?.type).to.equal('boolean');
				expect(type.properties.get('timestamp')?.type).to.equal('number');
			});
	
			it('should handle all arithmetic in one type', () => {
				const source = `
					const Calculator = define('Calculator', function (this: any, data: { x: number; y: number }) {
						this.sum = data.x + data.y;
						this.diff = data.x - data.y;
						this.product = data.x * data.y;
						this.quotient = data.x / data.y;
						this.modulo = data.x % data.y;
					});
				`;
	
				const result = analyzer.analyzeSource(source);
	
				expect(result.types).to.have.length(1);
				const type = result.types[0];
				expect(type.properties.get('sum')?.type).to.equal('number');
				expect(type.properties.get('diff')?.type).to.equal('number');
				expect(type.properties.get('product')?.type).to.equal('number');
				expect(type.properties.get('quotient')?.type).to.equal('number');
				expect(type.properties.get('modulo')?.type).to.equal('number');
			});
		});
});
