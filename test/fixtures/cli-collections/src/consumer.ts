import { Shop } from './models';
import type {
	ShopRegistry_Product,
	ShopRegistry_Product_Category,
} from '../.tactica/types';

// ---------------------------------------------------------------------------
// 1. Collection lookup resolves through the augmented ShopRegistry interface
// ---------------------------------------------------------------------------

const ProductCtor = Shop.lookup('Product');

const product = new ProductCtor({ productId : 'p1' });
const { productId } = product;

// @ts-expect-error — productId is required
new ProductCtor({});

// @ts-expect-error — productId must be a string
new ProductCtor({ productId : 42 });

// @ts-expect-error — unknown excess field
new ProductCtor({ productId : 'p2', nope : true });

// Dotted path straight from the collection root
const CategoryCtorDirect = Shop.lookup('Product.Category');
const directCategory = new CategoryCtorDirect({ categoryId : 'c0' });
const directCid: string = directCategory.categoryId;

// ---------------------------------------------------------------------------
// 2. Constructor-relative lookup
// ---------------------------------------------------------------------------

const CategoryCtor = ProductCtor.lookup('Category');
const category = new CategoryCtor({ categoryId : 'c1' });
const { categoryId } = category;
const inheritedProductId: string = category.productId;

// @ts-expect-error — categoryId is required
new CategoryCtor({});

// ---------------------------------------------------------------------------
// 3. Instance-side chain construction
// ---------------------------------------------------------------------------

const chained = new product.Category({ categoryId : 'c2' });
const chainedCid: string = chained.categoryId;
const chainedPid: string = chained.productId;

// @ts-expect-error — instance-side constructor still checks args
new product.Category({});

// ---------------------------------------------------------------------------
// 4. Looked-up instances are assignable to the generated aliases
// ---------------------------------------------------------------------------

const typedProduct: ShopRegistry_Product = product;
const typedCategory: ShopRegistry_Product_Category = category;

export {
	productId,
	directCid,
	categoryId,
	inheritedProductId,
	chainedCid,
	chainedPid,
	typedProduct,
	typedCategory,
};
