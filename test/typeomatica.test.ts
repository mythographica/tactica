'use strict';

import { expect } from 'chai';
import { MnemonicaAnalyzer } from '../src/analyzer';

describe('Typeomatica Patterns', () => {
	describe('@Strict decorator with mnemonica', () => {
		it('should detect @decorate with @Strict combination', () => {
			const code = `
import { decorate } from 'mnemonica';
import { Strict } from 'typeomatica';

@decorate({ blockErrors: true })
@Strict()
class MyDecoratedClass {
	field: number;
	constructor() {
		this.field = 123;
	}
}

@decorate(MyDecoratedClass, { strictChain: false })
class MyDecoratedSubClass {
	sub_field: number;
	constructor() {
		this.sub_field = 321;
	}
}
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');

			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include.members([
				'MyDecoratedClass',
				'MyDecoratedSubClass'
			]);

			const graph = analyzer.getGraph();
			const allTypes = graph.getAllTypes();
			const parentClass = allTypes.find(t => t.name === 'MyDecoratedClass');
			const subClass = allTypes.find(t => t.name === 'MyDecoratedSubClass');

			expect(subClass?.parent?.name).to.equal('MyDecoratedClass');
			expect(parentClass?.children.has('MyDecoratedSubClass')).to.be.true;
		});

		it('should handle @Strict with config in @decorate chain', () => {
			const code = `
import { decorate } from 'mnemonica';
import { Strict } from 'typeomatica';

const strictConfig = { strict: true };

@decorate()
@Strict(strictConfig)
class StrictWithDecorate {
	value: string;
	constructor() {
		this.value = 'test';
	}
}

const StrictType = define('StrictType', StrictWithDecorate);
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');

			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include.members([
				'StrictWithDecorate',
				'StrictType'
			]);
		});
	});

	describe('BaseClass with mnemonica integration', () => {
		it('should handle Object.setPrototypeOf with BaseClass and @decorate', () => {
			const code = `
import { decorate } from 'mnemonica';
import { BaseClass } from 'typeomatica';

const deep = { deep: true };

@decorate()
class BaseWithStrict {
	base_field = 555;
}

Object.setPrototypeOf(BaseWithStrict.prototype, new BaseClass(deep));

@decorate(BaseWithStrict)
class DerivedFromBase {
	field = 333;
}
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');

			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include.members([
				'BaseWithStrict',
				'DerivedFromBase'
			]);

			const graph = analyzer.getGraph();
			const allTypes = graph.getAllTypes();
			const baseType = allTypes.find(t => t.name === 'BaseWithStrict');
			const derivedType = allTypes.find(t => t.name === 'DerivedFromBase');

			expect(derivedType?.parent?.name).to.equal('BaseWithStrict');
			expect(baseType?.children.has('DerivedFromBase')).to.be.true;
		});

		it('should handle BasePrototype with define() and ConstructorFunction', () => {
			const code = `
import { define } from 'mnemonica';
import { BasePrototype, ConstructorFunction } from 'typeomatica';

const baseProto = BasePrototype({ strictAccessCheck: true });

const MyFn = function (this: any) {
	this.sub_sub_field = 123;
} as ConstructorFunction<{ sub_sub_field: number }>;

Object.setPrototypeOf(MyFn.prototype, new baseProto());

const MyFnType = define('MyFnType', MyFn);

@decorate(MyFnType)
class MyFnSubClass {
	field: number;
	constructor() {
		this.field = 456;
	}
}
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');

			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include.members([
				'MyFnType',
				'MyFnSubClass'
			]);
		});
	});

	describe('ConstructorFunction with define()', () => {
		it('should detect ConstructorFunction type casting with define()', () => {
			const code = `
import { define } from 'mnemonica';
import { ConstructorFunction } from 'mnemonica';

const MyFn = function (this: any) {
	this.sub_sub_field = 123;
} as ConstructorFunction<{ sub_sub_field: number }>;

const MyFnType = define('MyFnType', MyFn);

class MyFnSubClass {
	additionalField: string;
	constructor() {
		this.additionalField = 'test';
	}
}

const MySubFnType = MyFnType.define('MySubFnType', MyFnSubClass);
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');

			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include.members([
				'MyFnType',
				'MySubFnType'
			]);

			const graph = analyzer.getGraph();
			const allTypes = graph.getAllTypes();
			const parentType = allTypes.find(t => t.name === 'MyFnType');
			const subType = allTypes.find(t => t.name === 'MySubFnType');

			expect(subType?.parent?.name).to.equal('MyFnType');
			expect(parentType?.children.has('MySubFnType')).to.be.true;
		});
	});

	describe('Complex combined patterns from typeomatica/core tests', () => {
		it('should handle MyDecoratedClass pattern from core/test/decorate.ts', () => {
			const code = `
import { decorate } from 'mnemonica';
import { Strict } from 'typeomatica';

const deep = { deep: true };

@decorate({ blockErrors: true })
class MyDecoratedClass {
	DecoratedClassProp!: string;
	constructor() {
		this.DecoratedClassProp = 'decorated';
	}
}

@decorate(MyDecoratedClass, { strictChain: false })
class MyDecoratedSubClass {
	DecoratedSubClassProp!: number;
	constructor() {
		this.DecoratedSubClassProp = 123;
	}
}

@decorate(MyDecoratedSubClass)
class MyDecoratedSubSubClass {
	DecoratedSubSubClassProp!: boolean;
	constructor() {
		this.DecoratedSubSubClassProp = true;
	}
}
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');

			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include.members([
				'MyDecoratedClass',
				'MyDecoratedSubClass',
				'MyDecoratedSubSubClass'
			]);

			const graph = analyzer.getGraph();
			const allTypes = graph.getAllTypes();

			const class1 = allTypes.find(t => t.name === 'MyDecoratedClass');
			const class2 = allTypes.find(t => t.name === 'MyDecoratedSubClass');
			const class3 = allTypes.find(t => t.name === 'MyDecoratedSubSubClass');

			expect(class2?.parent?.name).to.equal('MyDecoratedClass');
			expect(class3?.parent?.name).to.equal('MyDecoratedSubClass');
			expect(class1?.children.has('MyDecoratedSubClass')).to.be.true;
			expect(class2?.children.has('MyDecoratedSubSubClass')).to.be.true;
		});

		it('should handle MyOtherDecoratedClass extending BaseClass', () => {
			const code = `
import { decorate } from 'mnemonica';
import { BaseClass, Strict } from 'typeomatica';

const deep = { deep: true };

@decorate()
class MyOtherDecoratedClass {
	OtherDecoratedProp!: string;
	constructor() {
		this.OtherDecoratedProp = 'other';
	}
}

Object.setPrototypeOf(MyOtherDecoratedClass.prototype, new BaseClass(deep));

@decorate(MyOtherDecoratedClass)
class MyOtherDecoratedSubClass {
	OtherSubProp!: number;
	constructor() {
		this.OtherSubProp = 456;
	}
}
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');

			expect(result.errors).to.have.length(0);
			expect(result.types.map(t => t.name)).to.include.members([
				'MyOtherDecoratedClass',
				'MyOtherDecoratedSubClass'
			]);
		});
	});

	describe('Typeomatica patterns should not break mnemonica detection', () => {
		it('should not produce errors when processing typeomatica imports', () => {
			const code = `
import { Strict, BaseClass, BasePrototype } from 'typeomatica';
import { define, decorate } from 'mnemonica';

// Typeomatica-only code that shouldn't break mnemonica detection
@Strict({ someProp: 123 })
class StrictOnlyClass {
	someProp!: number;
}

class BaseClassOnly extends BaseClass {
	field = 555;
}

// Mnemonica code should still be detected
const MnemonicaType = define('MnemonicaType', function(this: any) {
	this.mnemonicaField = 'test';
});
`;
			const analyzer = new MnemonicaAnalyzer();
			const result = analyzer.analyzeSource(code, 'test.ts');

			// Should not have errors from typeomatica code
			const typeomaticaErrors = result.errors.filter(e => 
				e.message.includes('typeomatica') || 
				e.message.includes('BaseClass') ||
				e.message.includes('Strict')
			);
			expect(typeomaticaErrors).to.have.length(0);

			// Should still detect mnemonica types
			expect(result.types.map(t => t.name)).to.include('MnemonicaType');
		});
	});
});
