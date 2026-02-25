'use strict';

import { expect } from 'chai';
import { MnemonicaAnalyzer } from '../src/analyzer';

describe('Tactica Example Files', () => {
	describe('index.ts patterns', () => {
		it('should detect UserType → AdminType → SuperAdminType hierarchy', () => {
			const code = `
import { define } from 'mnemonica';

const UserType = define('UserType', function (this: any) {
	this.name = '';
});

const AdminType = UserType.define('AdminType', function (this: any) {
	this.role = 'admin';
});

const SuperAdminType = AdminType.define('SuperAdminType', function (this: any) {
	this.isSystemAdmin = true;
});
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');
			
			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include.members([
				'UserType', 'AdminType', 'SuperAdminType'
			]);
			
			const graph = analyzer.getGraph();
			
			// Check all types exist
			const allTypes = graph.getAllTypes();
			expect(allTypes.some(t => t.name === 'UserType')).to.be.true;
			expect(allTypes.some(t => t.name === 'AdminType')).to.be.true;
			expect(allTypes.some(t => t.name === 'SuperAdminType')).to.be.true;
			
			// Check hierarchy
			const userType = allTypes.find(t => t.name === 'UserType');
			const adminType = allTypes.find(t => t.name === 'AdminType');
			const superAdminType = allTypes.find(t => t.name === 'SuperAdminType');
			
			expect(userType).to.exist;
			expect(adminType).to.exist;
			expect(superAdminType).to.exist;
			
			// UserType should have AdminType as child
			expect(userType?.children.has('AdminType')).to.be.true;
			
			// AdminType should have UserType as parent and SuperAdminType as child
			expect(adminType?.parent?.name).to.equal('UserType');
			expect(adminType?.children.has('SuperAdminType')).to.be.true;
			
			// SuperAdminType should have AdminType as parent
			expect(superAdminType?.parent?.name).to.equal('AdminType');
		});

		it('should detect @decorate() decorator', () => {
			const code = `
import { decorate } from 'mnemonica';

@decorate()
class Order {
	orderId: string = '';
	total: number = 0;
}
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');
			
			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include('Order');
			
			const orderType = result.types.find(t => t.name === 'Order');
			expect(orderType?.properties.has('orderId')).to.be.true;
			expect(orderType?.properties.has('total')).to.be.true;
		});
	});

	describe('decorators.ts patterns', () => {
		it('should detect @decorate() with parent class', () => {
			const code = `
import { decorate } from 'mnemonica';

@decorate()
class BaseEntity {
	id: string = '';
}

@decorate(BaseEntity)
class UserEntity {
	username: string = '';
}

@decorate(UserEntity)
class AdminEntity {
	role: string = 'admin';
}
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');
			
			expect(result.errors).to.have.length(0);
			
			const graph = analyzer.getGraph();
			const allTypes = graph.getAllTypes();
			
			const baseEntity = allTypes.find(t => t.name === 'BaseEntity');
			const userEntity = allTypes.find(t => t.name === 'UserEntity');
			const adminEntity = allTypes.find(t => t.name === 'AdminEntity');
			
			expect(baseEntity).to.exist;
			expect(userEntity).to.exist;
			expect(adminEntity).to.exist;
			
			expect(userEntity?.parent?.name).to.equal('BaseEntity');
			expect(adminEntity?.parent?.name).to.equal('UserEntity');
			
			expect(baseEntity?.children.has('UserEntity')).to.be.true;
			expect(userEntity?.children.has('AdminEntity')).to.be.true;
		});
	});

	describe('config-options.ts patterns', () => {
		it('should detect types with exposeInstanceMethods options', () => {
			const code = `
import { define } from 'mnemonica';

const StandardType = define('StandardType', function (this: any) {
	this.data = 'standard';
});

const HiddenMethodsType = define('HiddenMethodsType', function (this: any) {
	this.data = 'hidden';
}, { exposeInstanceMethods: false });

const HiddenTypeShorthand = define('HiddenTypeShorthand', function (this: any) {
	this.data = 'shorthand';
}, false);

const StandardSubtype = StandardType.define('StandardSubtype', function (this: any) {
	this.subtypeData = 'subtype';
});
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');
			
			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include.members([
				'StandardType',
				'HiddenMethodsType',
				'HiddenTypeShorthand',
				'StandardSubtype'
			]);
			
			const graph = analyzer.getGraph();
			const allTypes = graph.getAllTypes();
			const standardType = allTypes.find(t => t.name === 'StandardType');
			expect(standardType?.children.has('StandardSubtype')).to.be.true;
		});
	});

	describe('multi-file tracing', () => {
		it('should build complete graph from multiple files', () => {
			const analyzer = new MnemonicaAnalyzer();
			
			// Simulate multiple files
			const file1 = `
import { define } from 'mnemonica';
const UserType = define('UserType', function (this: any) {
	this.name = '';
});
`;
			const file2 = `
import { define } from 'mnemonica';
const ProductType = define('ProductType', function (this: any) {
	this.price = 0;
});
`;
			const file3 = `
import { decorate } from 'mnemonica';
@decorate()
class Order {
	orderId: string = '';
}
`;
			
			analyzer.analyzeSource(file1, 'src/users.ts');
			analyzer.analyzeSource(file2, 'src/products.ts');
			analyzer.analyzeSource(file3, 'src/orders.ts');
			
			const graph = analyzer.getGraph();
			const allTypes = graph.getAllTypes();
			
			expect(allTypes.map(t => t.name)).to.include.members([
				'UserType', 'ProductType', 'Order'
			]);
			
			// All should be roots since no parent relationships
			expect(graph.roots.size).to.equal(3);
		});
	});

	describe('type hierarchy tree output', () => {
		it('should correctly build complex hierarchy', () => {
			const code = `
import { define, decorate } from 'mnemonica';

// Define hierarchy
const ServiceType = define('ServiceType', function (this: any) {
	this.id = '';
});

const WebServiceType = ServiceType.define('WebServiceType', function (this: any) {
	this.endpoint = '';
});

const DatabaseServiceType = ServiceType.define('DatabaseServiceType', function (this: any) {
	this.connectionString = '';
});

// Decorator hierarchy
@decorate()
class BaseEntity {
	id: string = '';
}

@decorate(BaseEntity)
class UserEntity {
	email: string = '';
}
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');
			
			const graph = analyzer.getGraph();
			const allTypes = graph.getAllTypes();
			
			// Check ServiceType has two children
			const serviceType = allTypes.find(t => t.name === 'ServiceType');
			expect(serviceType?.children.size).to.equal(2);
			expect(serviceType?.children.has('WebServiceType')).to.be.true;
			expect(serviceType?.children.has('DatabaseServiceType')).to.be.true;
			
			// Check BaseEntity has UserEntity as child
			const baseEntity = allTypes.find(t => t.name === 'BaseEntity');
			expect(baseEntity?.children.has('UserEntity')).to.be.true;
			
			// Check UserEntity extends BaseEntity
			const userEntity = allTypes.find(t => t.name === 'UserEntity');
			expect(userEntity?.parent?.name).to.equal('BaseEntity');
		});
	});
});
