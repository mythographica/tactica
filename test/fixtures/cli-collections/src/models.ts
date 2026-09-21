import { createTypesCollection } from 'mnemonica';

export interface ShopRegistry {}

export interface ProductShape {
	productId: string;
}

export interface CategoryShape extends ProductShape {
	categoryId: string;
}

export const Shop = createTypesCollection<ShopRegistry>();

export const Product = Shop.define('Product', function (this: ProductShape, data: { productId: string }) {
	this.productId = data.productId;
});

export const Category = Product.define('Category', function (this: CategoryShape, data: { categoryId: string }) {
	this.categoryId = data.categoryId;
});
