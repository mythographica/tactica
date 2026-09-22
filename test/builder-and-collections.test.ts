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

	describe('collection two-pass stability and relative lookup', () => {
		const collectionSource = `
			import { createTypesCollection } from 'mnemonica';

			export interface ShopRegistry {}

			const Shop = createTypesCollection<ShopRegistry>();
			const Product = Shop.define('Product', function (this: any, data: { productId: string }) {
				this.productId = data.productId;
			});
			Product.define('Category', function (this: any, data: { categoryId: string }) {
				this.categoryId = data.categoryId;
			});
		`;

		it('should not duplicate collection types when the file is analyzed twice', () => {
			// The CLI runs a definitions pass, then resetUsages(), then a usages
			// pass re-analyzing every file. The collection id minted for a
			// variable must survive the second pass — a fresh one re-registers
			// every type under a new `collectionId::` prefix and the generator
			// emits each of them twice (TS2300 in the generated files).
			analyzer.analyzeSource(collectionSource, 'src/models.ts');
			analyzer.resetUsages();
			analyzer.analyzeSource(collectionSource, 'src/models.ts');

			expect(analyzer.getGraph().getAllTypes()).to.have.length(2);

			const generator = new TypesGenerator(analyzer.getGraph(), false, '.tactica');
			const types = generator.generateTypesFile().content;
			const registry = generator.generateTypeRegistry().content;

			expect(types.split('export type ShopRegistry_Product =')).to.have.length(2);
			expect(types.split('export type ShopRegistry_Product_Category =')).to.have.length(2);
			expect(registry.split('\'Product\':')).to.have.length(2);
			expect(registry.split('\'Product.Category\':')).to.have.length(2);
		});

		it('should not let class-body constructions clobber the root variable binding', () => {
			// Regression: `new Map()` in a class-body property initializer
			// walked up PAST the class boundary and rebound the root variable
			// to 'Map', so the later Definitions.define('DefinitionEntry')
			// lost its parent and the child became a bare default-collection
			// root (the name-only fallback cannot see collection types).
			const source = `
				import { createTypesCollection } from 'mnemonica';

				export interface BackendRegistry {}

				const Backend = createTypesCollection<BackendRegistry>();
				const Definitions = Backend.define('Definitions', class {
					private map: Map<string, object> = new Map();
				});
				const DefinitionEntry = Definitions.define('DefinitionEntry', function (this: any, data: { name: string }) {
					this.name = data.name;
				});
			`;

			const result = analyzer.analyzeSource(source, 'src/models.ts');

			expect(result.errors).to.have.length(0);
			const definitions = result.types.find(t => t.name === 'Definitions');
			const entry = result.types.find(t => t.name === 'DefinitionEntry');
			expect(definitions).to.exist;
			expect(entry).to.exist;
			expect(definitions?.collectionId).to.be.a('string');
			expect(entry?.parent).to.equal(definitions);
			expect(entry?.fullPath).to.equal(`${definitions?.fullPath ?? ''}.DefinitionEntry`);
		});

		it('should emit the Option B prefixed alias for graph types in member annotations', () => {
			// Regression: return-annotation resolution emitted the raw
			// `collectionId::Dotted_Path` fullPath (invalid TS) instead of the
			// registry-prefixed alias types.ts declares. The forward alias
			// resolves on the second pass, when the graph is complete.
			const source = `
				import { createTypesCollection } from 'mnemonica';

				export interface ShopRegistry {}

				type CategoryInstance = InstanceType<typeof Category>;
				const Shop = createTypesCollection<ShopRegistry>();
				const Product = Shop.define('Product', class {
					find (): CategoryInstance | undefined {
						return undefined;
					}
				});
				const Category = Product.define('Category', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
			`;

			analyzer.analyzeSource(source, 'src/models.ts');
			analyzer.resetUsages();
			const result = analyzer.analyzeSource(source, 'src/models.ts');

			expect(result.errors).to.have.length(0);
			const generator = new TypesGenerator(analyzer.getGraph(), false, '.tactica');
			const types = generator.generateTypesFile().content;

			expect(types).to.include('find: () => ShopRegistry_Product_Category | undefined');
			expect(types).to.not.match(/collection_\d+::/);
		});

		it('should target the collection home module for multi-file Option B registries', () => {
			// Regression: the augmentation used each TYPE's define file as the
			// declare-module target, so a registry interface declared at the
			// createTypesCollection() site (the only place it can live for a
			// multi-file collection) was never augmented and lookups stayed
			// untyped.
			const collectionFile = `
				import { createTypesCollection } from 'mnemonica';
				export interface ShopRegistry {}
				export const Shop = createTypesCollection<ShopRegistry>();
			`;
			const modelFile = `
				import { Shop } from './collections';
				export const Product = Shop.define('Product', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
				export const Category = Product.define('Category', function (this: any, data: { name: string }) {
					this.name = data.name;
				});
			`;

			analyzer.analyzeSource(collectionFile, 'src/collections.ts');
			analyzer.analyzeSource(modelFile, 'src/models.ts');

			const generator = new TypesGenerator(analyzer.getGraph(), false, '.tactica');
			const registry = generator.generateTypeRegistry().content;

			expect(registry).to.include('declare module \'../src/collections\'');
			expect(registry).to.include('\'Product\':');
			expect(registry).to.include('\'Product.Category\':');
			expect(registry).to.not.include('declare module \'../src/models\'');
		});

		it('should build the collections manifest: default first, custom in minting order', () => {
			const source = `
				import { define, createTypesCollection } from 'mnemonica';

				export interface ShopRegistry {}

				const Legacy = define('Legacy', function (this: any) {});
				const Shop = createTypesCollection<ShopRegistry>();
				Shop.define('Product', function (this: any, data: { id: string }) {
					this.id = data.id;
				});
				const Plain = createTypesCollection();
				Plain.define('Loose', function (this: any) {});
			`;

			analyzer.analyzeSource(source, 'src/app.ts');
			const manifest = analyzer.getCollectionsManifest();

			expect(manifest).to.have.length(3);
			expect(manifest[ 0 ]).to.deep.equal({
				id                : null,
				name              : 'defaultTypes',
				registryInterface : 'TypeRegistry',
				location          : null
			});
			expect(manifest[ 1 ].id).to.equal('collection_1');
			expect(manifest[ 1 ].name).to.equal('Shop');
			expect(manifest[ 1 ].registryInterface).to.equal('ShopRegistry');
			expect(manifest[ 1 ].location).to.match(/^src\/app\.ts:\d+:\d+$/);
			expect(manifest[ 2 ].id).to.equal('collection_2');
			expect(manifest[ 2 ].name).to.equal('Plain');
			// no Option-B interface -> the field stays absent, not null
			expect(manifest[ 2 ]).to.not.have.property('registryInterface');
		});

		it('should omit the default entry when no default-collection types exist', () => {
			const source = `
				import { createTypesCollection } from 'mnemonica';
				const Shop = createTypesCollection();
				Shop.define('Product', function (this: any) {});
			`;

			analyzer.analyzeSource(source, 'src/app.ts');
			const manifest = analyzer.getCollectionsManifest();

			expect(manifest).to.have.length(1);
			expect(manifest[ 0 ].name).to.equal('Shop');
		});

		it('should emit only the default entry for a default-only project', () => {
			const source = `
				import { define } from 'mnemonica';
				define('Legacy', function (this: any) {});
			`;

			analyzer.analyzeSource(source, 'src/app.ts');
			const manifest = analyzer.getCollectionsManifest();

			expect(manifest).to.have.length(1);
			expect(manifest[ 0 ].name).to.equal('defaultTypes');
			expect(manifest[ 0 ].id).to.be.null;
		});

		it('should resolve a constructor-relative lookup() inside a collection', () => {
			// ProductCtor is bound to a TYPE inside the collection, not to the
			// collection itself: lookup must go relative-first from that type,
			// not collapse to `<collectionId>::Category` (runtime semantics:
			// the type's own subtypes first, then the collection root).
			const source = `${collectionSource}
				const ProductCtor = Shop.lookup('Product');
				const CategoryCtor = ProductCtor.lookup('Category');
			`;

			analyzer.analyzeSource(source, 'src/models.ts');

			expect(analyzer.getResolutionErrors()).to.have.length(0);

			const product = analyzer.getGraph().getAllTypes()
				.find(t => t.name === 'Product');
			expect(product).to.exist;
			const collectionId = product!.collectionId!;

			const usages = analyzer.getUsages();
			expect(usages.has(`${collectionId}::Product`)).to.be.true;
			const categoryUsages = usages.get(`${collectionId}::Product.Category`);
			expect(categoryUsages).to.exist;
			expect(categoryUsages!.some(u => u.kind === 'lookup' && u.code.includes('ProductCtor.lookup'))).to.be.true;
		});

		it('should fall back to the collection root from a type-bound receiver', () => {
			const source = `${collectionSource}
				Shop.define('Util', function (this: any, data: { u: string }) {
					this.u = data.u;
				});
				const ProductCtor = Shop.lookup('Product');
				const UtilCtor = ProductCtor.lookup('Util');
			`;

			analyzer.analyzeSource(source, 'src/models.ts');

			expect(analyzer.getResolutionErrors()).to.have.length(0);

			const product = analyzer.getGraph().getAllTypes()
				.find(t => t.name === 'Product');
			const usages = analyzer.getUsages();
			const utilUsages = usages.get(`${product!.collectionId}::Util`);
			expect(utilUsages).to.exist;
			expect(utilUsages!.some(u => u.kind === 'lookup' && u.code.includes('ProductCtor.lookup'))).to.be.true;
		});

		it('should fail a constructor-relative lookup that resolves nowhere', () => {
			const source = `${collectionSource}
				const ProductCtor = Shop.lookup('Product');
				ProductCtor.lookup('Nope');
			`;

			analyzer.analyzeSource(source, 'src/models.ts');

			const errors = analyzer.getResolutionErrors();
			expect(errors).to.have.length(1);
			expect(errors[ 0 ].message).to.include('Nope');
		});
	});
});
