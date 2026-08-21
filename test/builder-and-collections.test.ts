import { expect } from 'chai';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { TypesGenerator } from '../src/generator';

describe('Builder pattern and custom collections', () => {
	let analyzer: MnemonicaAnalyzer;

	beforeEach(() => {
		analyzer = new MnemonicaAnalyzer();
	});

	describe('builder pattern on imported module object', () => {
		it('should detect mnemonica.define(...).define(...) chain', () => {
			const source = `
				import { mnemonica } from 'mnemonica';

				const App = mnemonica
					.define('User', function (this: any, data: { name: string }) {
						this.name = data.name;
					})
					.define('Admin', function (this: any, data: { role: string }) {
						this.role = data.role;
					});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(2);
			const user = result.types.find(t => t.fullPath === 'User');
			const admin = result.types.find(t => t.fullPath === 'User.Admin');
			expect(user).to.exist;
			expect(admin).to.exist;
			expect(user?.collectionId).to.be.undefined;
			expect(admin?.collectionId).to.be.undefined;
		});

		it('should detect aliased module import', () => {
			const source = `
				import { mnemonica as m } from 'mnemonica';

				m.define('User', function (this: any, data: { name: string }) {
					this.name = data.name;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[ 0 ].fullPath).to.equal('User');
			expect(result.types[ 0 ].collectionId).to.be.undefined;
		});

		it('should detect namespace import of mnemonica', () => {
			const source = `
				import * as mnemonica from 'mnemonica';

				mnemonica.define('User', function (this: any, data: { name: string }) {
					this.name = data.name;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[ 0 ].fullPath).to.equal('User');
		});

		it('should detect variable alias of module object chained with define()', () => {
			const source = `
				import { mnemonica } from 'mnemonica';

				const App = mnemonica;
				App.define('User', function (this: any, data: { name: string }) {
					this.name = data.name;
				});
				App.lookup('User').define('Admin', function (this: any, data: { role: string }) {
					this.role = data.role;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(2);
			expect(result.types.some(t => t.fullPath === 'User')).to.be.true;
			expect(result.types.some(t => t.fullPath === 'User.Admin')).to.be.true;
		});
	});

	describe('custom collections via createTypesCollection()', () => {
		it('should detect types defined on a collection variable', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				const MyCollection = createTypesCollection();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[ 0 ].name).to.equal('User');
			expect(result.types[ 0 ].collectionId).to.be.a('string');
		});

		it('should inherit collection for subtypes defined on a collection type', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				const MyCollection = createTypesCollection();
				const User = MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
				User.define('Admin', function (this: any, data: { role: string }) {
					this.role = data.role;
				});
			`;

			const result = analyzer.analyzeSource(source);

			const user = result.types.find(t => t.name === 'User' && t.collectionId);
			const admin = result.types.find(t => t.name === 'Admin' && t.parent === user);
			expect(user).to.exist;
			expect(admin).to.exist;
			expect(user?.collectionId).to.be.a('string');
			expect(admin?.collectionId).to.equal(user?.collectionId);
		});

		it('should keep collection when aliased to another variable', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				const CollA = createTypesCollection();
				const CollB = CollA;
				CollB.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.types).to.have.length(1);
			expect(result.types[ 0 ].name).to.equal('User');
			expect(result.types[ 0 ].collectionId).to.be.a('string');
		});

		it('should detect mnemonica.createTypesCollection() module object method', () => {
			const source = `
				import { mnemonica } from 'mnemonica';

				const MyCollection = mnemonica.createTypesCollection();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[ 0 ].name).to.equal('User');
			expect(result.types[ 0 ].collectionId).to.be.a('string');
		});

		it('should detect namespace import createTypesCollection()', () => {
			const source = `
				import * as mnemonica from 'mnemonica';

				const MyCollection = mnemonica.createTypesCollection();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[ 0 ].name).to.equal('User');
			expect(result.types[ 0 ].collectionId).to.be.a('string');
		});

		it('should detect aliased createTypesCollection import', () => {
			const source = `
				import { createTypesCollection as ctc } from 'mnemonica';

				const MyCollection = ctc();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[ 0 ].name).to.equal('User');
			expect(result.types[ 0 ].collectionId).to.be.a('string');
		});

		it('should isolate two collections defining a root with the same name', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				const CollA = createTypesCollection();
				const CollB = createTypesCollection();
				CollA.define('User', function (this: any, data: { a: string }) {
					this.a = data.a;
				});
				CollB.define('User', function (this: any, data: { b: string }) {
					this.b = data.b;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(2);
			const users = result.types.filter(t => t.name === 'User');
			expect(users).to.have.length(2);
			expect(users[ 0 ].collectionId).to.not.equal(users[ 1 ].collectionId);
		});

		it('should keep same-name collection roots in traversal and hierarchy', () => {
			// roots used to be keyed by plain name: the second 'User' overwrote
			// the first, and every roots-driven walk (generation, hierarchy)
			// silently lost the first collection's subtree
			const source = `
				import { createTypesCollection } from 'mnemonica';

				const CollA = createTypesCollection();
				const CollB = createTypesCollection();
				CollA.define('User', function (this: any, data: { a: string }) {
					this.a = data.a;
				});
				CollB.define('User', function (this: any, data: { b: string }) {
					this.b = data.b;
				});
				CollB.define('Group', function (this: any, data: { g: string }) {
					this.g = data.g;
				});
			`;

			analyzer.analyzeSource(source);
			const graph = analyzer.getGraph();

			expect(graph.roots.size).to.equal(3);

			const hierarchy = graph.toHierarchy();
			expect(hierarchy).to.have.length(3);
			const hierarchyNames = hierarchy.map(node => node.fullPath);
			expect(hierarchyNames.some(path => path.endsWith('::Group'))).to.be.true;
			expect(hierarchyNames.filter(path => path.endsWith('::User'))).to.have.length(2);
		});

		it('should emit both same-name Option B collection roots in types.ts', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				export interface RegistryA {}
				export interface RegistryB {}

				const CollA = createTypesCollection<RegistryA>();
				const CollB = createTypesCollection<RegistryB>();
				CollA.define('User', function (this: any, data: { a: string }) {
					this.a = data.a;
				});
				CollB.define('User', function (this: any, data: { b: string }) {
					this.b = data.b;
				});
			`;

			analyzer.analyzeSource(source);
			const generator = new TypesGenerator(analyzer.getGraph());
			const types = generator.generateTypesFile().content;

			expect(types).to.include('export type RegistryA_User');
			expect(types).to.include('export type RegistryB_User');
		});
	});

	describe('explicit-source define() and lookup()', () => {
		it('should handle define(source, "TypeName", handler) for collection root', () => {
			const source = `
				import { define, createTypesCollection } from 'mnemonica';

				const MyCollection = createTypesCollection();
				define(MyCollection, 'User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			const result = analyzer.analyzeSource(source);

			expect(result.errors).to.have.length(0);
			expect(result.types).to.have.length(1);
			expect(result.types[ 0 ].name).to.equal('User');
			expect(result.types[ 0 ].collectionId).to.be.a('string');
		});

		it('should handle define(source, "SubType", handler) for existing type', () => {
			const source = `
				import { define, createTypesCollection } from 'mnemonica';

				const MyCollection = createTypesCollection();
				const User = MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
				define(User, 'Admin', function (this: any, data: { role: string }) {
					this.role = data.role;
				});
			`;

			const result = analyzer.analyzeSource(source);

			const admin = result.types.find(t => t.name === 'Admin' && t.parent?.name === 'User');
			expect(admin).to.exist;
			expect(admin?.collectionId).to.be.a('string');
		});
	});

	describe('TypeRegistry generation', () => {
		it('should include builder types defined via mnemonica.define() in TypeRegistry', () => {
			const source = `
				import { mnemonica } from 'mnemonica';

				mnemonica
					.define('User', function (this: any, data: { name: string }) {
						this.name = data.name;
					})
					.define('Admin', function (this: any, data: { role: string }) {
						this.role = data.role;
					});
			`;

			analyzer.analyzeSource(source);
			const generator = new TypesGenerator(analyzer.getGraph());
			const registry = generator.generateTypeRegistry().content;

			expect(registry).to.include('\'User\':');
			expect(registry).to.include('\'User.Admin\':');
		});

		it('should NOT include collection types in global TypeRegistry', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				const MyCollection = createTypesCollection();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			analyzer.analyzeSource(source);
			const generator = new TypesGenerator(analyzer.getGraph());
			const registry = generator.generateTypeRegistry().content;

			expect(registry).not.to.include('\'User\':');
		});

		it('should include default types and exclude collection types when both are present', () => {
			const source = `
				import { mnemonica, createTypesCollection } from 'mnemonica';

				mnemonica.define('DefaultUser', function (this: any, data: { name: string }) {
					this.name = data.name;
				});

				const MyCollection = createTypesCollection();
				MyCollection.define('CollectionUser', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			analyzer.analyzeSource(source);
			const generator = new TypesGenerator(analyzer.getGraph());
			const registry = generator.generateTypeRegistry().content;

			expect(registry).to.include('\'DefaultUser\':');
			expect(registry).not.to.include('\'CollectionUser\':');
		});

		it('should NOT emit collection types in types.ts', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				const MyCollection = createTypesCollection();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			analyzer.analyzeSource(source);
			const generator = new TypesGenerator(analyzer.getGraph());
			const types = generator.generateTypesFile().content;

			expect(types).not.to.include('export type User');
			expect(types).not.to.include('id: string');
		});

		it('should detect the registry interface from createTypesCollection<Registry>()', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				export interface MyCollectionRegistry {}

				const MyCollection = createTypesCollection<MyCollectionRegistry>();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			const result = analyzer.analyzeSource(source);

			const user = result.types.find(t => t.name === 'User');
			expect(user).to.exist;
			expect(user?.registryInterfaceName).to.equal('MyCollectionRegistry');
		});

		it('should emit Option B collection types with prefixed names in types.ts', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				export interface MyCollectionRegistry {}

				const MyCollection = createTypesCollection<MyCollectionRegistry>();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			analyzer.analyzeSource(source);
			const generator = new TypesGenerator(analyzer.getGraph());
			const types = generator.generateTypesFile().content;

			expect(types).to.include('export type MyCollectionRegistry_User');
			expect(types).to.include('id: string');
		});

		it('should generate a per-collection registry augmentation', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				export interface MyCollectionRegistry {}

				const MyCollection = createTypesCollection<MyCollectionRegistry>();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			analyzer.analyzeSource(source, 'src/app-types.ts');
			const generator = new TypesGenerator(analyzer.getGraph(), false, '.tactica');
			const registry = generator.generateTypeRegistry().content;

			expect(registry).to.include('declare module');
			expect(registry).to.include('interface MyCollectionRegistry');
			expect(registry).to.include('\'User\':');
			expect(registry).to.include('MyCollectionRegistry_User');
		});

		it('should still exclude collection types from the global TypeRegistry', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				export interface MyCollectionRegistry {}

				const MyCollection = createTypesCollection<MyCollectionRegistry>();
				MyCollection.define('User', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			analyzer.analyzeSource(source);
			const generator = new TypesGenerator(analyzer.getGraph());
			const registry = generator.generateTypeRegistry().content;

			expect(registry).not.to.include('declare module \'mnemonica\' {\n\tinterface TypeRegistry {\n\t\t\'User\':');
		});

		it('should detect @MyCollection.decorate() as a collection root type', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';

				export interface MyCollectionRegistry {}

				const MyCollection = createTypesCollection<MyCollectionRegistry>();

				@MyCollection.decorate()
				class User {
					id: string;
					constructor(data: { id: string }) {
						this.id = data.id;
					}
				}
			`;

			const result = analyzer.analyzeSource(source);

			const user = result.types.find(t => t.name === 'User');
			expect(user).to.exist;
			expect(user?.registryInterfaceName).to.equal('MyCollectionRegistry');
		});
	});

	describe('usage tracking for builder APIs', () => {
		it('should track lookup(source, path) as a usage of the resolved type', () => {
			const defineSource = `
				import { mnemonica } from 'mnemonica';
				mnemonica.define('User', function () {});
			`;
			const usageSource = `
				import { lookup, mnemonica } from 'mnemonica';
				const UserCtor = lookup(mnemonica, 'User');
			`;

			analyzer.analyzeSource(defineSource);
			analyzer.resetUsages();
			analyzer.analyzeSource(usageSource);

			const usages = analyzer.getUsages();
			expect(usages.has('User')).to.be.true;
		});

		it('should track App.lookup("User") as a usage of User', () => {
			const source = `
				import { mnemonica, lookup } from 'mnemonica';

				const App = mnemonica.define('User', function () {});
				const UserCtor = App.lookup('User');
			`;

			analyzer.resetUsages();
			analyzer.analyzeSource(source);

			const usages = analyzer.getUsages();
			expect(usages.has('User')).to.be.true;
		});
	});
});
